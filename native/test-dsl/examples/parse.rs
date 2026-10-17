//! Exercise real source -> AST -> IR, without running semantic checking or LSP.
use denotate_editor::Document;
use denotate_ir::Sources;
use denotate_test_dsl::{
    lowering::{LoweringOutcome, lower},
    syntax::{self, ParseOutcome},
};
use std::process::ExitCode;

fn main() -> ExitCode {
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(error) => {
            eprintln!("Could not parse/lower the file: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<bool, Box<dyn std::error::Error>> {
    let path = std::env::args()
        .nth(1)
        .ok_or("expected an InputMapping file path")?;
    let text = std::fs::read_to_string(&path)?;
    let mut sources = Sources::new();
    let snapshot = sources.add(&path, 1, "test-dsl", text.as_str())?;
    let document = Document::new(&mut syntax::parser()?, text, 1, false);
    let at = |span: denotate_ir::SourceSpan, message: &str| {
        let position = document.position(span.byte_range().start);
        eprintln!(
            "{path}:{}:{}: {message}",
            position.line + 1,
            position.character + 1
        );
    };
    let ast = match syntax::project(&document, &sources, snapshot)? {
        ParseOutcome::Parsed(ast) => ast,
        ParseOutcome::SyntaxErrors(errors) => {
            for error in errors {
                at(error.span, &error.message);
            }
            eprintln!("No AST or IR produced; semantic checking is paused.");
            return Ok(false);
        }
    };
    match lower(&ast, &sources)? {
        LoweringOutcome::Lowered(ir) => println!(
            "Parsed {} declarations and {} mappings; lowered {} rules (including the library). Semantic checking not run.",
            ast.declarations.len(),
            ast.mappings.len(),
            ir.corpus.rules().count()
        ),
        LoweringOutcome::UserErrors(errors) => {
            for error in errors {
                at(error.span, &format!("{:?}", error.kind));
            }
            eprintln!("No IR produced; semantic checking is paused.");
            return Ok(false);
        }
    }
    Ok(true)
}
