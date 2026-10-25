use super::{Name, parse_name};
use crate::{SourceFile, ast};
use denotate_ir::Namespace;

#[test]
fn standalone_names_decode_qualification_quotes_and_generated_identity() {
    for (raw, namespace, text, generated) in [
        ("  default_checks\n", None, "default_checks", false),
        ("::default_checks", Some(vec![]), "default_checks", false),
        ("lib::checks", Some(vec!["lib"]), "checks", false),
        (
            "::'a::b'::'verification'",
            Some(vec!["a::b"]),
            "verification",
            false,
        ),
        (
            "'a\\'b'::'line\\n\\t\\r\\\\'",
            Some(vec!["a'b"]),
            "line\n\t\r\\",
            false,
        ),
        (
            "'é😀'::'check name'",
            Some(vec!["é😀"]),
            "check name",
            false,
        ),
        ("$helper", None, "$helper", true),
        ("'$helper'", None, "$helper", false),
        ("lib::$helper", Some(vec!["lib"]), "$helper", true),
        ("lib::007", Some(vec!["lib"]), "7", false),
        ("::-0", Some(vec![]), "0", false),
    ] {
        assert_eq!(
            parse_name(raw).unwrap(),
            Name {
                namespace: namespace.map(|parts| Namespace::new(parts).unwrap()),
                text: text.into(),
                generated,
            },
            "{raw:?}"
        );
    }
}

// The full grammar is an independent oracle for the standalone scanner. Keep
// statement wrapping confined to this test, never the CLI's production path.
fn grammar_name(raw: &str) -> Option<Name> {
    let raw = raw.trim();
    let source = SourceFile::new("test", 0, format!("domain {raw} = [];"));
    let scopes = ast::parse(&source).ok()?;
    let statements = scopes
        .iter()
        .flat_map(|s| &s.statements)
        .collect::<Vec<_>>();
    let [
        ast::Statement {
            decl: ast::Decl::Domain(name, values),
            ..
        },
    ] = statements.as_slice()
    else {
        return None;
    };
    (values.is_empty() && name.span == (7..7 + raw.len())).then(|| Name {
        namespace: name.namespace.clone(),
        text: name.text.clone(),
        generated: name.generated,
    })
}

#[test]
fn standalone_names_agree_with_the_grammar_and_reject_trailing_syntax() {
    let tokens = [
        "a",
        "A_1",
        "_a",
        "a-b",
        "é",
        "verification",
        "source",
        "group_by",
        "$helper",
        "$$helper",
        "$1",
        "007",
        "-01",
        "9223372036854775808",
        "'a::b'",
        "'verification'",
        "'$helper'",
        "'a\\'b'",
        "'a\\\\b'",
        "''",
        "'a\\q'",
        "'a\nb'",
        "'a\rb'",
        "'a\tb'",
        "'unterminated",
        "'a'junk'",
        "'a\\'",
    ];
    let mut cases = vec![
        "".into(),
        "::".into(),
        "a:::b".into(),
        "a::::b".into(),
        "a::".into(),
        ":::a".into(),
        "a :: b".into(),
        "a//comment".into(),
        "//comment\na".into(),
        "a = []; sort injected; domain b".into(),
        "a;".into(),
        "a b".into(),
    ];
    for token in tokens {
        cases.push(token.to_owned());
        cases.push(format!("::{token}"));
        cases.push(format!("lib::{token}"));
        cases.push(format!("{token}::checks"));
        for member in tokens {
            cases.push(format!("{token}::{member}"));
        }
    }
    for raw in cases {
        assert_eq!(parse_name(&raw).ok(), grammar_name(&raw), "{raw:?}");
    }
}
