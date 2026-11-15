//! Local, bounded JSONL recording. The checker lends snapshots synchronously;
//! formatting and IO stay here. No graph or cone survives a callback.
use denotate_check::*;
use denotate_ir::{OccurrenceId, VerificationDeclaration};
use denotate_ir_text::LoadedProgram;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{BufWriter, Write},
    time::{Duration, Instant},
};

// Independent diagnostic allowances, split so attempts cannot consume the final
// graph's allowance. These are aggregate per file, including all verifications.
const WORK: usize = 2_000_000;
const BYTES: usize = 32 * 1024 * 1024;
const TIME: Duration = Duration::from_secs(10);
#[derive(Default)]
struct Usage {
    work: usize,
    records: usize,
    bytes: usize,
    elapsed: Duration,
    text: usize,
    stopped: Option<String>,
}
struct Allowance {
    usage: Usage,
    records: usize,
}
impl Allowance {
    fn charge(&mut self, n: usize, start: Instant) -> Result<(), String> {
        if let Some(reason) = &self.usage.stopped {
            return Err(reason.clone());
        }
        self.usage.work = self.usage.work.saturating_add(n);
        if self.usage.work > WORK / 2 {
            return Err("diagnostic work allowance".into());
        }
        if self.usage.elapsed + start.elapsed() >= TIME / 2 {
            return Err("diagnostic active-time allowance".into());
        }
        Ok(())
    }
}

pub struct Dump {
    output: BufWriter<Box<dyn Write>>,
    attempts: Allowance,
    graph: Allowance,
    failed: Option<String>,
    snapshots: BTreeMap<u64, usize>,
    trace: super::trace::Trace,
}
impl Dump {
    pub fn open(path: &str, records: usize, trace: &super::trace::Trace) -> Option<Self> {
        let output = match File::create_new(path) {
            Ok(file) => file,
            Err(e) => {
                trace.warning(format!("component dump unavailable: {e}"));
                return None;
            }
        };
        Some(Self::new(output, records, trace))
    }
    pub(super) fn new(
        output: impl Write + 'static,
        records: usize,
        trace: &super::trace::Trace,
    ) -> Self {
        let mut dump = Self {
            output: BufWriter::new(Box::new(output)),
            attempts: Allowance {
                usage: Usage::default(),
                records: records / 2,
            },
            graph: Allowance {
                usage: Usage::default(),
                records: records - records / 2,
            },
            failed: None,
            snapshots: BTreeMap::new(),
            trace: trace.clone(),
        };
        dump.control(json!({"record":"header","version":1,"format":"denotate-component-jsonl", "containsProgramNames":true,
            "allowance":{"records":records,"work":WORK,"bytes":BYTES,"activeTimeMs":TIME.as_millis()},
            "allocation":"half attempts, half context and last graph; aggregate across verifications",
            "identity":"SHA-256 of semantic-key debug encoding, version 1; snapshot numbers are invocation-local"}));
        dump
    }
    fn control(&mut self, record: Value) {
        if self.failed.is_some() {
            return;
        }
        let result = serde_json::to_writer(&mut self.output, &record)
            .map_err(std::io::Error::other)
            .and_then(|_| self.output.write_all(b"\n"))
            .and_then(|_| self.output.flush());
        if let Err(e) = result {
            let reason = format!("component dump write failed: {e}");
            self.trace.warning(&reason);
            self.failed = Some(reason);
        }
    }
    pub fn capture(
        &mut self,
        p: &LoadedProgram,
        verification: &VerificationDeclaration,
        event: AdmissionDump<'_>,
    ) {
        if self.failed.is_some() {
            return;
        }
        let graph = matches!(event.event, AdmissionDumpEvent::Graph { .. });
        let start = Instant::now();
        let allowance = if graph {
            &mut self.graph
        } else {
            &mut self.attempts
        };
        // Control records remain small and available even after data truncation.
        // No traversal is performed to count unvisited records.
        let verification_key = identity(p.keys.verification(verification.id).unwrap());
        let section = if graph { "graph" } else { "attempts" };
        if let Some(reason) = &allowance.usage.stopped {
            if graph {
                let reason = reason.clone();
                self.control(json!({"record":"graph-end","verification":verification_key,"complete":false,"reason":reason,"omittedRecords":{"kind":"unknown"}}));
            }
            return;
        }
        let next = self.snapshots.len() + 1;
        let snapshot = *self.snapshots.entry(event.snapshot).or_insert(next);
        let mut formatter = Formatter {
            p,
            program: event.program,
            allowance,
            start,
            output: &mut self.output,
            verification: verification_key.clone(),
            snapshot: snapshot as u64,
            context: None,
        };
        let result = (|| -> Result<(), String> {
            match event.event {
                AdmissionDumpEvent::Graph { state, error } => {
                    formatter.graph(verification, state, error)
                }
                AdmissionDumpEvent::Guarded {
                    candidate,
                    literal,
                    cone,
                    implied,
                    before_atoms,
                    before_rules,
                    pruning,
                } => formatter.attempt(
                    candidate,
                    literal,
                    cone,
                    implied,
                    before_atoms,
                    before_rules,
                    pruning,
                ),
                AdmissionDumpEvent::GuardedOutcome {
                    rule,
                    occurrence,
                    stage,
                    state,
                    reason,
                } => {
                    let target = formatter.target(rule, occurrence)?;
                    formatter.emit(json!({"record":"attempt-outcome","target":target,"stage":stage,"state":state,
                    "reason":reason.map(|r|json!({"phase":r.phase,"resource":r.resource,"limit":r.details.limit,"demand":r.details.observed}))}))
                }
            }
        })();
        // `capture` is infallible to admission. A formatting or writing failure
        // produces only diagnostic status and never changes its result.
        formatter.allowance.usage.elapsed += start.elapsed();
        let written = formatter.allowance.usage.records;
        let context = formatter.context.take();
        if let Err(reason) = result {
            formatter.allowance.usage.stopped = Some(reason.clone());
            self.trace
                .warning(format!("component dump {section} truncated: {reason}"));
            self.control(json!({"record":"truncated","section":section,"verification":verification_key,"snapshot":snapshot,"context":context,"reason":reason,
                "writtenRecords":written,"omittedRecords":if reason=="diagnostic record allowance" || reason=="diagnostic byte allowance" {json!({"kind":"lower-bound","count":1})} else {json!({"kind":"unknown"})}}));
        }
    }
}

fn identity(key: &impl std::fmt::Debug) -> String {
    struct Hash(Sha256);
    impl std::fmt::Write for Hash {
        fn write_str(&mut self, s: &str) -> std::fmt::Result {
            self.0.update(s.as_bytes());
            Ok(())
        }
    }
    let mut hash = Hash(Sha256::new());
    std::fmt::write(&mut hash, format_args!("{key:?}")).unwrap();
    format!("{:x}", hash.0.finalize())
}
macro_rules! emit {
    ($s:ident, $value:expr) => {{
        let value = $value;
        $s.emit(value)
    }};
}
struct Formatter<'a> {
    p: &'a LoadedProgram,
    program: &'a GroundProgram,
    allowance: &'a mut Allowance,
    start: Instant,
    output: &'a mut BufWriter<Box<dyn Write>>,
    verification: String,
    snapshot: u64,
    context: Option<Value>,
}
impl Formatter<'_> {
    fn charge(&mut self, n: usize) -> Result<(), String> {
        self.allowance.charge(n, self.start)
    }
    fn text(&mut self, n: usize) -> Result<(), String> {
        self.allowance.usage.text = self.allowance.usage.text.saturating_add(n);
        if self.allowance.usage.text > BYTES / 2 {
            return Err("diagnostic text allowance".into());
        }
        self.charge(1 + n / 64)
    }
    fn items(&mut self, n: usize) -> Result<(), String> {
        if n > 16_384 {
            return Err("diagnostic collection allowance".into());
        }
        self.charge(1)
    }
    fn emit(&mut self, mut value: Value) -> Result<(), String> {
        self.charge(1)?;
        if self.allowance.usage.records >= self.allowance.records {
            return Err("diagnostic record allowance".into());
        }
        value["verification"] = json!(self.verification);
        value["snapshot"] = json!(self.snapshot);
        if let Some(context) = &self.context {
            value["context"] = context.clone();
        }
        let bytes = serde_json::to_vec(&value).map_err(|e| e.to_string())?;
        if self.allowance.usage.bytes.saturating_add(bytes.len() + 1) > BYTES / 2 {
            return Err("diagnostic byte allowance".into());
        }
        self.output
            .write_all(&bytes)
            .and_then(|_| self.output.write_all(b"\n"))
            .map_err(|e| format!("write failure: {e}"))?;
        self.allowance.usage.records += 1;
        self.allowance.usage.bytes += bytes.len() + 1;
        // Incremental delivery, including just before an interrupted operation.
        self.output
            .flush()
            .map_err(|e| format!("write failure: {e}"))
    }
    fn key(&mut self, a: &GroundAtom) -> Result<AtomKey, String> {
        self.charge(1 + a.arguments.len())?;
        AtomKey::from_atom(&self.p.keys, a).map_err(|e| e.to_string())
    }
    fn qualified(&mut self, id: OccurrenceId, name: String) -> Result<String, String> {
        let mut prefix = Vec::new();
        for part in self.p.corpus.namespace(id).unwrap().segments() {
            self.text(part.len())?;
            prefix.push(denotate_ir_text::spelling(
                part,
                denotate_ir_text::NameKind::Identifier,
            ));
        }
        Ok(format!("{}::{name}", prefix.join("::")))
    }
    fn atom(&mut self, a: &GroundAtom) -> Result<Value, String> {
        let key = self.key(a)?;
        let relation = self.p.corpus.relation(a.relation).unwrap();
        self.text(relation.name.len())?;
        let relation_name = self.qualified(
            relation.id.into(),
            if self.p.corpus.is_generated_relation(relation.id) {
                relation.name.clone()
            } else {
                denotate_ir_text::spelling(&relation.name, denotate_ir_text::NameKind::Identifier)
            },
        )?;
        let mut values = Vec::new();
        for c in &a.arguments {
            self.charge(1)?;
            let constant = self.p.corpus.constant(*c).unwrap();
            self.text(constant.name.len())?;
            values.push(self.qualified(
                (*c).into(),
                denotate_ir_text::spelling(&constant.name, denotate_ir_text::NameKind::Constant),
            )?);
        }
        Ok(json!({"id":identity(&key),"name":format!("{relation_name}({})",values.join(", "))}))
    }
    fn instance(&mut self, id: GroundRuleId) -> Result<InstanceKey, String> {
        let rule = self
            .program
            .original_rule(id)
            .ok_or("missing original instance")?;
        self.charge(
            1 + rule
                .body
                .iter()
                .map(|l| 1 + l.term.atom.arguments.len())
                .sum::<usize>()
                + rule.head.atom.arguments.len(),
        )?;
        InstanceKey::from_rule(&self.p.corpus, &self.p.keys, rule).map_err(|e| e.to_string())
    }
    fn occurrence(&mut self, id: OccurrenceId) -> Result<String, String> {
        self.charge(1)?;
        Ok(identity(
            self.p.keys.bindings().key(id).map_err(|e| e.to_string())?,
        ))
    }
    fn target(&mut self, rule: GroundRuleId, occurrence: OccurrenceId) -> Result<Value, String> {
        Ok(
            json!({"rule":identity(&self.instance(rule)?),"occurrence":self.occurrence(occurrence)?}),
        )
    }
    fn location(&mut self, id: impl Into<OccurrenceId>) -> Result<Value, String> {
        self.charge(1)?;
        let Some(origin) = self.p.provenance.origins(id).first() else {
            return Ok(Value::Null);
        };
        let Ok(source) = self.p.sources.snapshot(origin.span.snapshot()) else {
            return Ok(Value::Null);
        };
        self.text(source.uri.len())?;
        Ok(
            json!({"uri":source.uri,"byteStart":origin.span.byte_range().start,"byteEnd":origin.span.byte_range().end}),
        )
    }
    fn literal(&mut self, l: &GroundLiteral) -> Result<Value, String> {
        let settled = self
            .program
            .component_for(&l.term.atom)
            .map_or(true, |c| c.blocked_by.is_empty());
        Ok(
            json!({"atom":self.atom(&l.term.atom)?,"polarity":if l.polarity==Polarity::Negative {"negative"} else {"positive"},
            "state":if settled {"settled"} else {"unresolved"},"occurrence":self.occurrence(l.term.occurrence)?,"source":self.location(l.term.occurrence)?}),
        )
    }
    fn expression(
        &mut self,
        e: &SettledExpression<GroundAtom>,
        depth: usize,
    ) -> Result<Value, String> {
        self.charge(1)?;
        if depth > 128 {
            return Err("diagnostic expression-depth allowance".into());
        }
        Ok(match e {
            SettledExpression::Constant(v) => json!({"constant":v}),
            SettledExpression::Atom(a) => json!({"atom":self.atom(a)?}),
            SettledExpression::Not(c) => json!({"not":self.expression(c, depth+1)?}),
            SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                self.items(cs.len())?;
                let mut children = Vec::new();
                for c in cs {
                    children.push(self.expression(c, depth + 1)?);
                }
                if matches!(e, SettledExpression::All(_)) {
                    json!({"all":children})
                } else {
                    json!({"any":children})
                }
            }
        })
    }
    fn rule(&mut self, r: &GroundRule, summary: Option<&ProducerSummary>) -> Result<Value, String> {
        let mut premises = Vec::new();
        self.items(r.body.len().saturating_add(r.replacements.len()))?;
        for l in &r.body {
            premises.push(self.literal(l)?);
        }
        let mut replacements = Vec::new();
        for r in &r.replacements {
            replacements.push(json!({"occurrence":self.occurrence(r.occurrence)?,"expression":self.expression(&r.expression,0)?}));
        }
        let mut settled = Vec::new();
        if let Some(summary) = summary {
            for p in &summary.settled {
                settled.push(self.literal(&p.literal)?);
            }
        } else {
            settled.extend(premises.iter().filter(|p| p["state"] == "settled").cloned());
        }
        Ok(
            json!({"id":identity(&self.instance(r.id)?),"head":self.atom(&r.head.atom)?,"source":self.location(r.source)?,
            "premises":premises,"settledPremises":settled,"replacements":replacements,
            "guardMeaning":"conjunction of signed settled premises and replacement expressions; dependency reads are not a formula"}),
        )
    }
    fn ordered_atoms<'a>(
        &mut self,
        atoms: impl IntoIterator<Item = &'a GroundAtom>,
    ) -> Result<Vec<&'a GroundAtom>, String> {
        let mut keyed = Vec::new();
        for a in atoms {
            self.items(keyed.len() + 1)?;
            keyed.push((self.key(a)?, a));
        }
        keyed.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(keyed.into_iter().map(|(_, a)| a).collect())
    }
    fn graph(
        &mut self,
        v: &VerificationDeclaration,
        state: &str,
        error: Option<&CheckError>,
    ) -> Result<(), String> {
        emit!(
            self,
            json!({"record":"graph-begin","state":state,"error":error.map(ToString::to_string),"lastCommitted":true})
        )?;
        let mut components = Vec::new();
        let mut ordered_atoms = 0usize;
        for c in self.program.residual_components() {
            self.charge(1)?;
            if c.cycle.is_none() {
                continue;
            }
            ordered_atoms = ordered_atoms.saturating_add(c.atoms.len());
            self.items(ordered_atoms)?;
            let atoms = self.ordered_atoms(&c.atoms)?;
            if let Some(first) = atoms.first() {
                self.items(components.len() + 1)?;
                components.push((self.key(first)?, c, atoms));
            }
        }
        components.sort_by(|a, b| a.0.cmp(&b.0));
        let count = components.len();
        for (representative, c, atoms) in components {
            let component = identity(&representative);
            self.context = Some(json!({"component":component}));
            emit!(
                self,
                json!({"record":"component","id":component,"atoms":atoms.len()})
            )?;
            for a in atoms {
                let atom = self.atom(a)?;
                emit!(self, json!({"record":"atom","atom":atom}))?;
            }
            let mut rules = Vec::new();
            for r in self.program.residual_component_producers(c.id) {
                self.items(rules.len() + 1)?;
                rules.push((self.instance(r.id)?, r));
            }
            rules.sort_by(|a, b| a.0.cmp(&b.0));
            for (_, r) in rules {
                let rule = self.rule(r, None)?;
                emit!(self, json!({"record":"rule","rule":rule}))?;
                self.edges(r)?;
            }
        }
        self.context = None;
        emit!(
            self,
            json!({"record":"structure-end", "complete":true,"components":count})
        )?;
        self.context(v)?;
        emit!(
            self,
            json!({"record":"graph-end","complete":true,"components":count,"omittedRecords":{"kind":"exact","count":0}})
        )
    }
    fn context(&mut self, v: &VerificationDeclaration) -> Result<(), String> {
        let mut assumptions = Vec::new();
        for id in &v.assumptions {
            self.charge(1)?;
            assumptions.push((
                self.p.keys.assumption(*id).map_err(|e| e.to_string())?,
                self.p.corpus.assumption(*id).unwrap(),
            ));
        }
        assumptions.sort_by(|a, b| a.0.cmp(b.0));
        emit!(
            self,
            json!({"record":"context","name":super::name(self.p.corpus.namespace(v.id).unwrap(), &v.name),"selectedAssumptions":assumptions.len(),"worldMeaning":"conjunction of these selected restrictions"})
        )?;
        for (key, a) in assumptions {
            let restriction = &a.restriction;
            emit!(
                self,
                json!({"record":"assumption","id":identity(key),"name":super::name(self.p.corpus.namespace(a.id).unwrap(),&a.name),
                "kind":format!("{:?}",restriction.kind()),"relation":identity(self.p.keys.relation(restriction.relation()).unwrap()),"groupBy":restriction.group_by(),"source":self.location(a.id)?})
            )?;
            // Membership belongs to an explicitly selected restriction only.
            // No inferred exclusivity, and no Cartesian product enumeration.
            if restriction.kind().has_uniqueness() {
                let mut groups = BTreeMap::<Vec<denotate_ir::ConstantKey>, Vec<&GroundAtom>>::new();
                let atoms: Box<dyn Iterator<Item = &GroundAtom>> =
                    if self.p.corpus.relation(restriction.relation()).unwrap().role
                        == denotate_ir::RelationRole::Input
                    {
                        Box::new(self.program.input_atoms())
                    } else {
                        Box::new(self.program.atoms())
                    };
                for atom in atoms {
                    self.charge(1)?;
                    if atom.relation != restriction.relation() {
                        continue;
                    }
                    let key = self.key(atom)?;
                    let group = restriction
                        .group_by()
                        .iter()
                        .map(|i| key.arguments[*i].clone())
                        .collect();
                    self.items(groups.len() + 1)?;
                    let members = groups.entry(group).or_default();
                    self.items(members.len() + 1)?;
                    members.push(atom);
                }
                for (group, atoms) in groups {
                    let mut members = Vec::new();
                    for atom in self.ordered_atoms(atoms)? {
                        members.push(self.atom(atom)?);
                    }
                    emit!(
                        self,
                        json!({"record":"exclusive-group","assumption":identity(key),"group":identity(&group),"members":members})
                    )?;
                }
            }
        }
        Ok(())
    }
    fn edges(&mut self, rule: &GroundRule) -> Result<(), String> {
        for literal in &rule.body {
            let from = self.atom(&rule.head.atom)?;
            let to = self.literal(literal)?;
            emit!(
                self,
                json!({"record":"dependency","consumer":from,"premise":to,"rule":identity(&self.instance(rule.id)?)})
            )?;
        }
        for r in &rule.replacements {
            let mut stack = vec![(r.expression.as_ref(), false)];
            while let Some((e, negative)) = stack.pop() {
                self.charge(1)?;
                match e {
                    SettledExpression::Atom(atom) => {
                        let from = self.atom(&rule.head.atom)?;
                        let to = self.atom(atom)?;
                        emit!(
                            self,
                            json!({"record":"dependency","consumer":from,"provider":to,"polarity":if negative {"negative"} else {"positive"},"replacement":self.occurrence(r.occurrence)?})
                        )?;
                    }
                    SettledExpression::Not(c) => stack.push((c, !negative)),
                    SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                        self.items(stack.len().saturating_add(cs.len()))?;
                        self.charge(cs.len())?;
                        stack.extend(cs.iter().rev().map(|c| (c.as_ref(), negative)));
                    }
                    SettledExpression::Constant(_) => {}
                }
            }
        }
        Ok(())
    }
    fn attempt(
        &mut self,
        candidate: &ProducerSummary,
        literal: &GroundLiteral,
        cone: &GuardedCone<&ProducerSummary>,
        implied: Option<&ImpliedGuardProof>,
        before_atoms: Option<usize>,
        before_rules: Option<usize>,
        pruning: Option<&str>,
    ) -> Result<(), String> {
        let mut live_atoms = BTreeSet::new();
        let mut live_producers = 0;
        for p in &cone.producers {
            self.charge(1)?;
            if p.live {
                live_producers += 1;
                self.items(live_atoms.len() + 1)?;
                live_atoms.insert(&p.rule.head.atom);
            }
        }
        let target = self.target(candidate.rule.id, literal.term.occurrence)?;
        self.context = Some(json!({"target":target}));
        let guard = self.rule(&candidate.rule, Some(candidate))?;
        let implied_expression = implied
            .map(|i| self.expression(&i.expression, 0))
            .transpose()?;
        emit!(
            self,
            json!({"record":"attempt","target":target,"premise":self.literal(literal)?,"guard":guard,"impliedGuard":implied_expression,
            "domainMeaning":"selected W AND guard.settledPremises AND guard.replacements AND impliedGuard",
            "before":{"atoms":before_atoms,"producers":before_rules},"after":{"atoms":cone.atoms.len(),"producers":cone.producers.len(),"liveAtoms":live_atoms.len(),"liveProducers":live_producers},
            "pruning":pruning,"fallback":pruning.filter(|p|*p!="complete"),"relaxedRule":cone.relaxed_rule.map(|r|self.instance(r).map(|k|identity(&k))).transpose()?})
        )?;
        if let Some(implied) = implied {
            for premise in &implied.premises {
                let literal = self.literal(&premise.literal)?;
                for source in &premise.producers {
                    let rule = self.rule(&source.rule, Some(source))?;
                    emit!(
                        self,
                        json!({"record":"implied-source","premise":literal,"producer":rule})
                    )?;
                }
            }
        }
        for atom in self.ordered_atoms(&cone.atoms)? {
            let a = self.atom(atom)?;
            emit!(
                self,
                json!({"record":"cone-atom","atom":a,"live":live_atoms.contains(atom)})
            )?;
        }
        let mut producers = Vec::new();
        for p in &cone.producers {
            self.items(producers.len() + 1)?;
            producers.push((self.instance(p.rule.id)?, p));
        }
        producers.sort_by(|a, b| a.0.cmp(&b.0));
        let mut reads = BTreeSet::new();
        for (_, p) in producers {
            let rule = self.rule(&p.rule, Some(p))?;
            emit!(
                self,
                json!({"record":"cone-producer","live":p.live,"producer":rule})
            )?;
            if p.live {
                for settled in &p.settled {
                    self.charge(1 + settled.literal.term.atom.arguments.len())?;
                    reads.insert(settled.literal.term.atom.clone());
                }
                self.replacement_reads(&p.rule, &mut reads)?;
            }
        }
        let mut reasons = Vec::new();
        for (id, reason) in &cone.pruning.reasons {
            self.items(reasons.len() + 1)?;
            reasons.push((self.instance(*id)?, reason));
        }
        reasons.sort_by(|a, b| a.0.cmp(&b.0));
        for (key, reason) in reasons {
            let reason = match reason {
                GuardedDeadReason::SettledCondition => json!({"kind":"settled-condition"}),
                GuardedDeadReason::Positive(a) => {
                    json!({"kind":"positive-premise","atom":self.atom(a)?})
                }
                GuardedDeadReason::Negative {
                    atom,
                    exact_producers,
                } => {
                    let mut sources = Vec::new();
                    for r in exact_producers {
                        sources.push(self.instance(*r)?);
                    }
                    sources.sort();
                    json!({"kind":"negative-premise","atom":self.atom(atom)?,"exactProducers":sources.iter().map(identity).collect::<Vec<_>>()})
                }
            };
            emit!(
                self,
                json!({"record":"dead-producer","producer":identity(&key),"reason":reason})
            )?;
        }
        let mut sources = Vec::new();
        for s in &cone.pruning.sources {
            self.items(sources.len() + 1)?;
            sources.push((self.instance(s.rule.id)?, s));
        }
        sources.sort_by(|a, b| a.0.cmp(&b.0));
        for (_, source) in sources {
            let rule = self.rule(&source.rule, Some(source))?;
            emit!(self, json!({"record":"pruning-source","producer":rule}))?;
        }
        // G is part of the attempted domain, including inferred settled leaves.
        // W remains separately described by the selected restrictions.
        for p in &candidate.settled {
            self.charge(1 + p.literal.term.atom.arguments.len())?;
            reads.insert(p.literal.term.atom.clone());
        }
        self.replacement_reads(&candidate.rule, &mut reads)?;
        if let Some(implied) = implied {
            self.expression_reads(&implied.expression, &mut reads)?;
        }
        self.inputs(reads)?;
        emit!(
            self,
            json!({"record":"attempt-data-end","complete":true,"omittedRecords":{"kind":"exact","count":0}})
        )
    }
    fn reads(&mut self, r: &GroundRule, reads: &mut BTreeSet<GroundAtom>) -> Result<(), String> {
        for l in &r.body {
            self.charge(1 + l.term.atom.arguments.len())?;
            reads.insert(l.term.atom.clone());
        }
        self.replacement_reads(r, reads)
    }
    fn replacement_reads(
        &mut self,
        r: &GroundRule,
        reads: &mut BTreeSet<GroundAtom>,
    ) -> Result<(), String> {
        for r in &r.replacements {
            self.expression_reads(&r.expression, reads)?;
        }
        Ok(())
    }
    fn expression_reads(
        &mut self,
        expression: &SettledExpression<GroundAtom>,
        reads: &mut BTreeSet<GroundAtom>,
    ) -> Result<(), String> {
        let mut stack = vec![expression];
        while let Some(e) = stack.pop() {
            self.charge(1)?;
            match e {
                SettledExpression::Atom(a) => {
                    self.charge(a.arguments.len())?;
                    self.items(reads.len() + 1)?;
                    reads.insert(a.clone());
                }
                SettledExpression::Not(c) => stack.push(c),
                SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                    self.items(stack.len().saturating_add(cs.len()))?;
                    self.charge(cs.len())?;
                    stack.extend(cs.iter().map(AsRef::as_ref));
                }
                _ => {}
            }
        }
        Ok(())
    }
    fn inputs(&mut self, mut pending: BTreeSet<GroundAtom>) -> Result<(), String> {
        let mut visited = BTreeSet::new();
        let mut inputs = BTreeMap::new();
        while let Some(a) = pending.pop_first() {
            self.items(visited.len() + 1)?;
            if !visited.insert(a.clone()) {
                continue;
            }
            if self.p.corpus.relation(a.relation).unwrap().role == denotate_ir::RelationRole::Input
            {
                inputs.insert(self.key(&a)?, a);
                continue;
            }
            if let Ok(c) = self.program.component_for(&a) {
                for r in self.program.residual_component_producers(c.id) {
                    self.charge(1)?;
                    if r.head.atom == a {
                        self.reads(r, &mut pending)?;
                    }
                }
            }
        }
        for (_, a) in inputs {
            let a = self.atom(&a)?;
            emit!(
                self,
                json!({"record":"cone-input","input":a,"meaning":"structural dependency, not Boolean guard"})
            )?;
        }
        Ok(())
    }
}
