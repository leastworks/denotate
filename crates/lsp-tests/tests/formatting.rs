mod support;
use serde_json::{json, Value};
use support::{apply_edits, Client};

fn format(client: &mut Client, uri: &str) -> Value {
    client.request(
        "textDocument/formatting",
        json!({"textDocument":{"uri":uri},
        "options":{"tabSize":4,"insertSpaces":true}}),
    )
}

// Independent of the recovered CST and the formatter: retain identifiers,
// punctuation, line comments and every unrecognized character in source order.
fn tokens(text: &str) -> Vec<String> {
    let mut chars = text.chars().peekable();
    let mut result = vec![];
    while let Some(ch) = chars.next() {
        if " \t\r\n".contains(ch) {
            continue;
        }
        let mut token = ch.to_string();
        if ch == '/' && chars.peek() == Some(&'/') {
            token.push(chars.next().unwrap());
            while chars.peek().is_some_and(|c| *c != '\r' && *c != '\n') {
                token.push(chars.next().unwrap());
            }
        } else if ch.is_ascii_alphabetic() || ch == '_' {
            while chars
                .peek()
                .is_some_and(|c| c.is_ascii_alphanumeric() || *c == '_')
            {
                token.push(chars.next().unwrap());
            }
        } else if ch == ':' && chars.peek() == Some(&'-') {
            token.push(chars.next().unwrap());
        }
        result.push(token);
    }
    result
}

#[test]
fn formatting_has_golden_style_preserves_tokens_and_is_idempotent() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let raw = "module example;\nsort Slot;\nconst a,b:Slot;\nrelation r( slot:Slot );\nr( D ):-r( D ),!r( D );\n";
    let expected = "module example;\nsort Slot;\nconst a, b: Slot;\nrelation r(slot: Slot);\nr(D) :-\n    r(D),\n    !r(D);\n";
    for (index, eol) in ["\n", "\r\n", "\r"].iter().enumerate() {
        let source = raw.replace('\n', eol);
        client.change(&uri, 2 + index as i64 * 2, &source);
        let result = format(&mut client, &uri);
        assert!(!result.as_array().unwrap().is_empty());
        let formatted = apply_edits(&source, result.as_array().unwrap());
        assert_eq!(formatted, expected.replace('\n', eol));
        assert_eq!(tokens(&source), tokens(&formatted));
        std::fs::write(client.workspace.path().join("example.den"), &formatted).unwrap();
        client.change(&uri, 3 + index as i64 * 2, &formatted);
        assert_eq!(format(&mut client, &uri), json!([]));
    }
    client.shutdown();
}

#[test]
fn formatting_broken_fixtures_preserves_comments_and_unrecognized_text() {
    for workspace in [
        "base/01-missing-semicolon",
        "base/02-unclosed-paren",
        "base/03-truncated-argument",
        "base/09-formatting-recovery",
    ] {
        let mut client = Client::start(workspace);
        for file in ["computation.den", "example.den"] {
            if !client.workspace.path().join(file).exists() {
                continue;
            }
            let (uri, source) = client.open(file);
            let result = format(&mut client, &uri);
            let formatted = apply_edits(&source, result.as_array().unwrap());
            assert_eq!(tokens(&source), tokens(&formatted), "{workspace}/{file}");
            if workspace == "base/09-formatting-recovery" && file == "example.den" {
                assert_ne!(source, formatted, "useful edits around broken region");
                assert!(formatted
                    .contains("relation available(slot: Slot); // Keep this trailing comment."));
                assert!(formatted.contains(
                    "available(a); , @ // Unexpected punctuation and an unrecognized character."
                ));
            }
            client.change(&uri, 2, &formatted);
            assert_eq!(
                format(&mut client, &uri),
                json!([]),
                "idempotence: {workspace}/{file}"
            );
        }
        client.shutdown();
    }
}

#[test]
fn malformed_formatting_has_an_exact_golden_and_preserves_comment_attachment() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let source = "module example;\nrelation r( x:Slot ); // café 🦀   \nr( a ); , @ // broken\n// standalone\nrelation s( x:Slot );\n";
    client.change(&uri, 2, source);
    let formatted = apply_edits(source, format(&mut client, &uri).as_array().unwrap());
    assert_eq!(formatted, "module example;\nrelation r(x: Slot); // café 🦀   \nr( a ); , @ // broken\n// standalone\nrelation s(x: Slot);\n");
    assert_eq!(tokens(source), tokens(&formatted));
    client.shutdown();
}

#[test]
fn formatting_ranges_after_an_astral_comment_use_utf16_columns() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let source = "module example; // café 🦀\n       sort Slot;\n";
    client.change(&uri, 2, source);
    let result = format(&mut client, &uri);
    let utf16 = source.lines().next().unwrap().encode_utf16().count();
    assert!(
        result
            .as_array()
            .unwrap()
            .iter()
            .any(|edit| edit["range"]["start"] == json!({"line":0,"character":utf16})),
        "{result}"
    );
    assert_eq!(
        apply_edits(source, result.as_array().unwrap()),
        "module example; // café 🦀\nsort Slot;\n"
    );
    client.shutdown();
}

#[test]
fn selection_formatting_never_edits_outside_the_requested_range() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let source = "module example;\nsort Slot;\nrelation r( x:Slot );\nrelation s( x:Slot );\n";
    client.change(&uri, 2, source);
    let result = client.request(
        "textDocument/rangeFormatting",
        json!({"textDocument":{"uri":uri},
        "options":{"tabSize":4,"insertSpaces":true}, "range":{"start":{"line":2,"character":0},
        "end":{"line":2,"character":21}}}),
    );
    assert!(!result.as_array().unwrap().is_empty());
    for edit in result.as_array().unwrap() {
        assert_eq!(edit["range"]["start"]["line"], 2);
        assert_eq!(edit["range"]["end"]["line"], 2);
    }
    assert_eq!(
        apply_edits(source, result.as_array().unwrap()),
        "module example;\nsort Slot;\nrelation r(x: Slot);\nrelation s( x:Slot );\n"
    );
    client.shutdown();
}
