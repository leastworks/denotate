//! No parser or LSP: select a hand-built, source-spanned AST and use public APIs.
#[path = "../tests/support/mod.rs"]
mod support;
use denotate_check::*;
use denotate_test_dsl::presentation;
use support::*;

fn main() {
    if let Err(error) = run() {
        if matches!(
            error.downcast_ref::<CheckError>(),
            Some(CheckError::LimitExceeded { .. })
        ) {
            eprintln!("Inconclusive: {error}");
        } else {
            eprintln!("Creator-facing failure: {error}");
        }
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "overlap".into());
    let fixture = match mode.as_str() {
        "overlap" => Fixture::overlap(),
        "mixed" => Fixture::mixed(false, false),
        "requires-c" => Fixture::mixed(true, false),
        "fixed" => Fixture::mixed(true, true),
        "exclusive" => Fixture::exclusive(),
        "redundant" => Fixture::redundant(),
        _ => {
            return Err(
                "expected overlap, mixed, requires-c, fixed, exclusive or redundant".into(),
            );
        }
    };
    let lowered = fixture.lower();
    let limits = Limits::default();
    let AnalysisOutcome::Complete(ground) =
        GroundProgram::prepare_checked(&lowered.corpus, &domains(&lowered), &limits)?
    else {
        println!("Inconclusive: preparation budget exhausted.");
        return Ok(());
    };
    let rewrite_start = std::time::Instant::now();
    let ground = ground.admit(&limits)?;
    let rewrite_elapsed = rewrite_start.elapsed();
    let AnalysisOutcome::Complete(meaning) = ground.symbolic_checked(&limits)? else {
        println!("Inconclusive: symbolic evaluation budget exhausted.");
        return Ok(());
    };
    let AnalysisOutcome::Complete(report) = meaning.verify_checked(&limits)? else {
        println!("Inconclusive: checking budget exhausted.");
        return Ok(());
    };
    let diagnostics = presentation::present(&lowered, &report, &fixture.sources, "test-dsl")?;
    let warnings = denotate_test_dsl::warnings::present_rewrites(
        &lowered,
        &ground,
        &fixture.sources,
        "test-dsl",
    )?;
    println!("{}", fixture.text);
    for warning in &warnings {
        println!("{:?} warning: {}", warning.owner, warning.message);
        if let Some(span) = warning.primary {
            println!("  at `{}`", fixture.sources.text(span)?);
        }
        if let Some(edit) = &warning.edit {
            println!(
                "  Suggested deletion: `{}`",
                fixture.sources.text(edit.span)?
            );
        }
    }
    println!(
        "Whole-program admissibility: {}",
        if report.whole_program_admitted() {
            "established"
        } else {
            "incomplete (unsupported cycle)"
        }
    );
    for diagnostic in &diagnostics {
        let source = fixture.sources.snapshot(diagnostic.primary.snapshot())?;
        let prefix = &source.text[..diagnostic.primary.byte_range().start];
        let line = prefix.bytes().filter(|b| *b == b'\n').count() + 1;
        let column = prefix.rsplit('\n').next().unwrap_or("").chars().count() + 1;
        println!("\n{}:{line}:{column}: {}", source.uri, diagnostic.message);
        for note in &diagnostic.notes {
            println!("  {note}");
        }
        for origin in &diagnostic.related {
            println!(
                "  {}: `{}` @ bytes {:?}",
                origin.role,
                fixture.sources.text(origin.span)?,
                origin.span.byte_range()
            );
        }
    }
    let show = |a: &GroundAtom| {
        format!(
            "{}({})",
            lowered.corpus.relation(a.relation).unwrap().name,
            a.arguments
                .iter()
                .map(|id| lowered.corpus.constant(*id).unwrap().name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    for group in &report.groups {
        let key = group
            .group
            .key
            .iter()
            .map(|id| lowered.corpus.constant(*id).unwrap().name.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        println!("\nGroup {key}:");
        match &group.outcome {
            VerifiedOutcome::Inconclusive(cause) => println!("  Inconclusive: {cause:?}"),
            VerifiedOutcome::Proved => println!("  Proved over every permitted input snapshot."),
            VerifiedOutcome::Unsupported => {
                println!("  Unsupported: dependency cone touches an unresolved component.")
            }
            VerifiedOutcome::Counterexample(example) => {
                println!("  Replayed: {:?}", example.replay_scope);
                for (label, facts) in [
                    ("present", &example.observation.present),
                    ("absent", &example.observation.absent),
                ] {
                    println!(
                        "  {label}: {}",
                        facts.iter().map(&show).collect::<Vec<_>>().join(", ")
                    );
                }
                let mut steps: Vec<_> = example.evidence.iter().collect();
                steps.sort_by_key(|(_, step)| step.order);
                println!("  Grounded evidence:");
                for (fact, step) in steps {
                    match &step.evidence {
                        GroundEvidence::Input => println!("    {} [input snapshot]", show(fact)),
                        GroundEvidence::Derived { rule, premises } => {
                            println!(
                                "    {}{}{};",
                                show(&rule.head.atom),
                                if rule.body.is_empty() { "" } else { " :- " },
                                rule.body
                                    .iter()
                                    .map(|l| format!(
                                        "{}{}",
                                        if l.polarity == Polarity::Negative {
                                            "!"
                                        } else {
                                            ""
                                        },
                                        show(&l.term.atom)
                                    ))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            );
                            for premise in premises {
                                if let PremiseEvidence::Discharged {
                                    literal_occurrence,
                                    proof,
                                } = premise
                                {
                                    println!(
                                        "      {literal_occurrence:?} discharged by {proof:?}"
                                    );
                                }
                                if let PremiseEvidence::Absent { fact, provider, .. } = premise {
                                    println!("      {} absent; provider {provider:?}", show(fact));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    for region in &report.unresolved {
        println!(
            "\nReported cycle (all {} rule instances):",
            region.rules.len()
        );
        for edge in &region.cycle.edges {
            println!(
                "  {} depends on {}{}",
                show(&edge.consumer),
                if edge.polarity == Polarity::Negative {
                    "!"
                } else {
                    ""
                },
                show(&edge.provider)
            );
        }
    }
    let ms = |d: std::time::Duration| d.as_secs_f64() * 1000.0;
    println!(
        "\nCosts (ms): grounding {:.3}, stratification {:.3}, rewrites {:.3}, symbolic {:.3}, properties {:.3}, witness {:.3}, replay {:.3}, evidence {:.3}",
        ms(ground.metrics().grounding),
        ms(ground.metrics().admissibility),
        ms(rewrite_elapsed),
        ms(meaning.metrics().elapsed),
        ms(report.property_metrics.elapsed),
        ms(report.finding_metrics.witness),
        ms(report.finding_metrics.replay),
        ms(report.finding_metrics.evidence)
    );
    println!(
        "All obligations proved: {}",
        report.all_obligations_proved()
    );
    Ok(())
}
