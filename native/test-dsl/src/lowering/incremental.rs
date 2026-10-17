//! Per-document lowering cache. No spans, arenas or worker state enter Salsa.
use super::{LoweringOutcome, Result, assembly, projection, recipe::Recipe, semantic::*};
use crate::ast::{Kind, Program};
use denotate_ir::Sources;
use salsa::Setter;
use serde::Serialize;
use std::{
    collections::BTreeMap,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    time::Instant,
};

// Retain forms for repair/undo within this document session. Closing drops the
// entire database; there is no bounded-memory claim while it remains open.
#[salsa::interned(revisions = usize::MAX)]
struct Form<'db> {
    #[returns(ref)]
    content: Arc<SemanticStatement>,
}

#[salsa::input]
struct DeclarationInput {
    #[returns(ref)]
    forms: Vec<Arc<SemanticStatement>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DeclarationData {
    names: Names,
    errors: Vec<PathDiagnostic>,
}

enum Query {
    Recipe,
    Declarations,
    Resolve,
    Validate,
}

#[salsa::db]
trait Db: salsa::Database {
    fn record(&self, query: Query);
}

#[salsa::db]
#[derive(Clone, Default)]
struct Database {
    storage: salsa::Storage<Self>,
    counts: Option<Arc<[AtomicU64; 4]>>,
}
#[salsa::db]
impl salsa::Database for Database {}
#[salsa::db]
impl Db for Database {
    fn record(&self, query: Query) {
        if let Some(counts) = &self.counts {
            counts[query as usize].fetch_add(1, Ordering::Relaxed);
        }
    }
}

#[salsa::tracked(returns(ref))]
fn recipe(db: &dyn Db, form: Form<'_>) -> Recipe {
    db.record(Query::Recipe);
    Recipe::lower(form.content(db).clone())
}

#[salsa::tracked(returns(ref))]
fn declarations(db: &dyn Db, input: DeclarationInput) -> DeclarationData {
    db.record(Query::Declarations);
    let mut duplicates = BTreeMap::new();
    let keys: Vec<_> = input
        .forms(db)
        .iter()
        .map(|form| {
            let duplicate = duplicates.entry(form).or_insert(0);
            let key = StatementKey {
                form: form.clone(),
                duplicate: *duplicate,
            };
            *duplicate += 1;
            key
        })
        .collect();
    let (names, errors) = Names::collect(&keys);
    DeclarationData { names, errors }
}

#[salsa::tracked]
fn resolve(db: &dyn Db, input: DeclarationInput, name: String, kind: Kind) -> Resolution {
    db.record(Query::Resolve);
    declarations(db, input).names.resolve(&name, kind)
}

#[salsa::tracked(returns(ref))]
fn validate(db: &dyn Db, input: DeclarationInput, form: Form<'_>) -> Vec<ValidationDiagnostic> {
    db.record(Query::Validate);
    validate_form(form.content(db), |name, kind| {
        resolve(db, input, name.into(), kind).clone()
    })
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct QueryCounts {
    pub recipe: u64,
    pub declarations: u64,
    pub resolve: u64,
    pub validate: u64,
}

/// Last call's wall time. Queries includes input synchronization, interning,
/// cached query access and binding diagnostics to current occurrence paths.
#[derive(Debug, Default, Clone, Copy, Serialize)]
pub struct Timings {
    pub projection_ns: u64,
    pub queries_ns: u64,
    pub assembly_attribution_ns: u64,
}

#[derive(Debug, Default, Clone, Copy, Serialize)]
pub struct Stats {
    pub queries: QueryCounts,
    pub declaration_updates: u64,
    pub assemblies: u64,
    pub last: Timings,
}

/// Owned by one open document on the server thread, never sent to the worker.
pub struct Session {
    db: Database,
    input: DeclarationInput,
    stats: Stats,
}
impl Default for Session {
    fn default() -> Self {
        Self::new(false)
    }
}
impl Session {
    /// Instrumentation is opt-in for tests/measurement, not ordinary editing.
    pub fn new(instrument: bool) -> Self {
        let db = Database {
            counts: instrument.then(|| Arc::new(Default::default())),
            ..Default::default()
        };
        let input = DeclarationInput::new(&db, vec![]);
        Self {
            db,
            input,
            stats: Stats::default(),
        }
    }

    pub fn stats(&self) -> Stats {
        let mut stats = self.stats;
        if let Some(c) = &self.db.counts {
            let [recipe, declarations, resolve, validate] =
                std::array::from_fn(|i| c[i].load(Ordering::Relaxed));
            stats.queries = QueryCounts {
                recipe,
                declarations,
                resolve,
                validate,
            };
        }
        stats
    }

    pub fn lower(&mut self, program: &Program, sources: &Sources) -> Result<LoweringOutcome> {
        self.stats.last = Timings::default();
        let start = self.clock();
        let projection = projection::project(program, sources)?;
        self.stats.last.projection_ns = elapsed(start);
        let start = self.clock();
        let declared = projection
            .statements
            .iter()
            .filter_map(|s| {
                matches!(s.key.form.as_ref(), SemanticStatement::Declaration { .. })
                    .then(|| s.key.form.clone())
            })
            .collect::<Vec<_>>();
        // In 0.28.5 even constructing the setter starts a revision.
        if self.input.forms(&self.db) != &declared {
            self.input.set_forms(&mut self.db).to(declared);
            if self.db.counts.is_some() {
                self.stats.declaration_updates += 1;
            }
        }
        let forms: Vec<_> = projection
            .statements
            .iter()
            .map(|s| Form::new(&self.db, s.key.form.clone()))
            .collect();
        let declarations = declarations(&self.db, self.input);
        let mut errors = declarations.errors.clone();
        for (source, &form) in projection.statements.iter().zip(&forms) {
            if !matches!(
                source.key.form.as_ref(),
                SemanticStatement::Declaration { .. }
            ) {
                errors.extend(
                    declarations
                        .names
                        .bind(&source.key, validate(&self.db, self.input, form))?,
                );
            }
        }
        // Gate the whole current snapshot, including duplicate declarations.
        // A recipe cache hit does not establish that the program is valid.
        if !errors.is_empty() {
            let errors = projection.diagnostics(&errors)?;
            self.stats.last.queries_ns = elapsed(start);
            return Ok(LoweringOutcome::UserErrors(errors));
        }
        let recipes: Vec<_> = forms.iter().map(|&form| recipe(&self.db, form)).collect();
        self.stats.last.queries_ns = elapsed(start);
        let start = self.clock();
        if self.db.counts.is_some() {
            self.stats.assemblies += 1;
        }
        let lowered = assembly::assemble(&projection, &recipes, sources)?;
        self.stats.last.assembly_attribution_ns = elapsed(start);
        Ok(LoweringOutcome::Lowered(lowered))
    }

    fn clock(&self) -> Option<Instant> {
        self.db.counts.as_ref().map(|_| Instant::now())
    }
}

fn elapsed(start: Option<Instant>) -> u64 {
    start.map_or(0, |t| t.elapsed().as_nanos().min(u64::MAX as u128) as u64)
}
