// Neutral completion workload: format recognition, guarded blocks and field values.
export function guardedSchema(options = {}) {
  const cfg = {sets: 8, depth: 2, fanout: 5, stmts: 3, triggers: 1, values: 2, reads: 1,
    outs: 5, splice: 25, self: 50, impossible: 0, ...options};
  for (const [key, value] of Object.entries(cfg)) {
    if (!Number.isSafeInteger(value) || value < 0) throw Error(`invalid guarded-schema ${key}`);
  }
  if (!cfg.sets || !cfg.depth || !cfg.fanout || !cfg.values || !cfg.reads || cfg.splice > 100 || cfg.self > 100 || cfg.impossible > 1) throw Error('invalid guarded-schema shape');
  const widths = cfg.blocks === undefined
    ? Array.from({length:cfg.depth},(_,d)=>cfg.fanout ** (d+1))
    : Array.from({length:cfg.depth},(_,d)=>Math.floor(cfg.blocks/cfg.depth)+(d<cfg.blocks%cfg.depth?1:0));
  if (widths.some(n=>!Number.isSafeInteger(n)||n<1)) throw Error('fixed blocks must cover every depth');
  const nested = widths.reduce((a,b)=>a+b,0), count = cfg.sets*(nested+1)+1;
  if (count > 200000) throw Error('guarded-schema generation exceeds 200000 blocks');
  cfg.blocks = nested;
  cfg.elements ??= Math.max(cfg.sets+1,Math.ceil(count*4/9));
  cfg.tasks ??= Math.max(1,Math.ceil(cfg.elements/4));
  if (!cfg.elements || !cfg.tasks) throw Error('elements and tasks must be positive');
  const lines = [];
  const add = x=>lines.push(x);
  const constants = (sort, names) => {add(`sort ${sort};`); if(names.length)add(`const ${names.join(',')}: ${sort};`);};
  const names=(prefix,n)=>Array.from({length:n},(_,i)=>`${prefix}${i}`);
  constants('Format',names('format_',cfg.sets));
  constants('Block',['global',...names('block_',count-1)]);
  constants('Element',['type_field',...names('element_',cfg.elements)]);
  constants('Value',[...names('tag_',cfg.sets),...Array.from({length:cfg.elements},(_,e)=>names(`value_${e}_`,cfg.values)).flat()]);
  constants('Statement',names('statement_',cfg.sets + cfg.sets*nested*cfg.stmts));
  constants('Task',names('task_',cfg.tasks));
  constants('Output',names('output_',cfg.tasks*cfg.outs));
  add(`relation format_root(f:Format,b:Block);
relation format_statement(f:Format,c:Statement);
relation leaf(f:Format);
relation block_parent(b:Block,p:Block);
relation statement_block(c:Statement,b:Block);
relation statement_element(c:Statement,e:Element);
relation statement_value(c:Statement,v:Value);
relation block_expected(b:Block,e:Element);
relation block_task(b:Block,t:Task);
relation task_output(t:Task,o:Output,e:Element);
relation compared(e:Element,v:Value);
relation result_candidate(e:Element,v:Value);
relation candidate(e:Element,v:Value);
candidate(E,V) :- compared(E,V);
input observed_value(e:Element,v:Value) within candidate;
input result_value(e:Element,v:Value) within result_candidate;
relation accepted_field(e:Element);
accepted_field(type_field);
accepted_field(E) :- block_expected(B,E),block_active(B);
relation element_value(e:Element,v:Value);
element_value(E,V) :- observed_value(E,V),accepted_field(E);
element_value(E,V) :- written_value(E,V);
relation element_present(e:Element);
element_present(E) :- element_value(E,V);
relation written_value(e:Element,v:Value);
written_value(E,V) :- computes(E),result_value(E,V);
relation computes(e:Element);
computes(E) :- task_output(T,O,E),task_active(T);
relation task_active(t:Task);
task_active(T) :- block_task(B,T),block_active(B);
relation statement_satisfied(c:Statement);
statement_satisfied(C) :- statement_element(C,E),statement_value(C,V),element_value(E,V);
relation term_holds(f:Format);
term_holds(F) :- engaged(),format_statement(F,C),statement_satisfied(C),type_matches(F);
relation type_matches(f:Format);
relation format_recognized(f:Format);
format_recognized(F) :- term_holds(F);
relation engaged();
engaged() :- format_recognized(F);
relation block_active(b:Block);
block_active(B) :- format_root(F,B),format_recognized(F)${cfg.impossible ? ",control_present()" : ""};
block_active(global) :- engaged(),global_guard()${cfg.impossible ? ",control_present()" : ""};${cfg.impossible ? "\nrelation control_present();" : ""}
relation global_guard();
global_guard() :- element_value(type_field,V);
relation recognized();
recognized() :- leaf(F),format_recognized(F);
relation violated(c:Statement);
violated(C) :- statement_block(C,B),block_active(B),!statement_satisfied(C);
assumption unique_observed: at_most_one(observed_value,group_by:(e));
assumption unique_results: at_most_one(result_value,group_by:(e));
obligation no_violations: empty(violated);
verification checks {semantics:completion;hypothesis:recognized;decisions:[format_recognized,accepted_field];assumptions:[unique_observed,unique_results];obligations:[no_violations];}`);
  for(let e=0;e<cfg.elements;e++) for(let v=0;v<cfg.values;v++)add(`compared(element_${e},value_${e}_${v});`);
  for(let t=0;t<cfg.tasks;t++) for(let o=0;o<cfg.outs;o++) {
    const e=(t*cfg.outs+o)%cfg.elements;
    add(`task_output(task_${t},output_${t*cfg.outs+o},element_${e});`);
  }
  add('result_candidate(E,V) :- task_output(T,O,E),compared(E,V);');
  const globalFields = new Set(Array.from({length:Math.floor(cfg.elements*cfg.splice/100)},(_,i)=>i));
  let b=0,c=cfg.sets;
  for(let f=0;f<cfg.sets;f++) {
    const root=b++, e=f%cfg.elements;
    add(`leaf(format_${f});format_root(format_${f},block_${root});format_statement(format_${f},statement_${f});
statement_element(statement_${f},element_${e});statement_value(statement_${f},value_${e}_0);
compared(type_field,tag_${f});type_matches(format_${f}) :- element_value(type_field,tag_${f});`);
    if(f*100<cfg.sets*cfg.self) { globalFields.delete(e);add(`block_expected(block_${root},element_${e});`); }
    else globalFields.add(e);
    let parents=[root];
    for(let d=0;d<cfg.depth;d++) {
      const next=[];
      for(let j=0;j<widths[d];j++) {
        const id=b++, parent=parents[j%parents.length]; next.push(id);
        add(`block_parent(block_${id},block_${parent});relation $condition_${id}();
block_active(block_${id}) :- block_active(block_${parent}),$condition_${id}();`);
        const tests=Array.from({length:cfg.reads},(_,k)=>{
          const x=(id*7+k*11)%cfg.elements;return `element_value(element_${x},value_${x}_${(id+k)%cfg.values})`;
        });
        add(`$condition_${id}() :- ${tests.join(',')};`);
        // A deterministic mix of shared terms and absence guards; no random seed.
        if(id%5===0) add(`$condition_${id}() :- term_holds(format_${(f+1)%cfg.sets});`);
        if(id%7===0) add(`$condition_${id}() :- !element_present(element_${(id*7)%cfg.elements});`);
        for(let k=0;k<cfg.stmts;k++) {
          const x=(id*3+k)%cfg.elements;
          add(`statement_block(statement_${c},block_${id});statement_element(statement_${c},element_${x});statement_value(statement_${c},value_${x}_${k%cfg.values});block_expected(block_${id},element_${x});`); c++;
        }
        for(let k=0;k<cfg.triggers;k++) add(`block_task(block_${id},task_${(id+k)%cfg.tasks});`);
      }
      parents=next;
    }
  }
  for(const e of [...globalFields].sort((a,b)=>a-b)) add(`block_expected(global,element_${e});`);
  return {source:lines.join('\n')+'\n',shape:{...cfg,totalBlocks:count,nestedBlocks:cfg.sets*nested,conditionSites:cfg.sets*nested,statementRows:cfg.sets*nested*cfg.stmts}};
}
