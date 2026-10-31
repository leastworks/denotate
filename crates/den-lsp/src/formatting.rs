//! Conservative whitespace edits; an independent raw-source lexer checks safety.
use crate::syntax::Document;
use lsp_types::Range;
use serde_json::{json, Value};
use std::collections::HashSet;

#[derive(Debug, PartialEq, Eq)]
struct Lexeme {
    start: usize,
    end: usize,
    kind: &'static str,
    standalone: bool,
}

fn whitespace(ch: char) -> bool {
    matches!(ch, ' ' | '\t' | '\r' | '\n')
}

fn lex(source: &str) -> Vec<Lexeme> {
    let mut result = vec![];
    let mut offset = 0;
    while offset < source.len() {
        let ch = source[offset..].chars().next().unwrap();
        if whitespace(ch) {
            offset += ch.len_utf8();
            continue;
        }
        let start = offset;
        let kind;
        if source[offset..].starts_with("//") {
            kind = "comment";
            offset += source[offset..]
                .find(['\r', '\n'])
                .unwrap_or(source.len() - offset);
        } else if matches!(ch, '\'' | '"') {
            kind = "quoted";
            offset += ch.len_utf8();
            while offset < source.len() {
                let next = source[offset..].chars().next().unwrap();
                offset += next.len_utf8();
                if next == '\\' {
                    if let Some(escaped) = source[offset..].chars().next() {
                        offset += escaped.len_utf8();
                    }
                } else if next == ch {
                    break;
                }
            }
        } else if ch.is_ascii_alphabetic() || ch == '_' {
            kind = "identifier";
            offset += 1;
            while source
                .as_bytes()
                .get(offset)
                .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_')
            {
                offset += 1;
            }
        } else if ch.is_ascii_digit()
            || (ch == '-'
                && source
                    .as_bytes()
                    .get(offset + 1)
                    .is_some_and(u8::is_ascii_digit))
        {
            kind = "integer";
            offset += 1;
            while source
                .as_bytes()
                .get(offset)
                .is_some_and(u8::is_ascii_digit)
            {
                offset += 1;
            }
        } else if source[offset..].starts_with(":-") || source[offset..].starts_with("::") {
            kind = "punctuation";
            offset += 2;
        } else {
            kind = if "(),;:!{}[]=#$".contains(ch) {
                "punctuation"
            } else {
                "unknown"
            };
            offset += ch.len_utf8();
        }
        let standalone = source[..start]
            .rsplit(['\r', '\n'])
            .next()
            .unwrap_or("")
            .chars()
            .all(whitespace);
        result.push(Lexeme {
            start,
            end: offset,
            kind,
            standalone: kind == "comment" && standalone,
        });
    }
    result
}

fn fingerprint(source: &str) -> Vec<(&'static str, &str, bool)> {
    lex(source)
        .into_iter()
        .map(|token| {
            (
                token.kind,
                &source[token.start..token.end],
                token.standalone,
            )
        })
        .collect()
}

fn endings(source: &str) -> Vec<&str> {
    let mut result = vec![];
    let mut cursor = 0;
    while cursor < source.len() {
        if source[cursor..].starts_with("\r\n") {
            result.push("\r\n");
            cursor += 2;
        } else if source.as_bytes()[cursor] == b'\r' {
            result.push("\r");
            cursor += 1;
        } else if source.as_bytes()[cursor] == b'\n' {
            result.push("\n");
            cursor += 1;
        } else {
            cursor += source[cursor..].chars().next().unwrap().len_utf8();
        }
    }
    result
}

pub fn format(doc: &Document, selection: Option<Range>) -> Value {
    let source = &doc.text;
    let tokens = lex(source);
    let mut damaged = HashSet::new();
    for diagnostic in doc.diagnostics() {
        for line in diagnostic.range.start.line..=diagnostic.range.end.line {
            damaged.insert(line);
        }
    }
    for token in &tokens {
        if token.kind == "unknown" {
            damaged.insert(doc.position(token.start).line);
        }
    }
    let eols = endings(source);
    let default_eol = eols.first().copied().unwrap_or("\n");
    let mut edits: Vec<(usize, usize, String)> = vec![];
    // Only declaration blocks introduce indentation. Origin maps use braces too.
    fn blocks(
        node: tree_sitter::Node<'_>,
        opens: &mut HashSet<usize>,
        closes: &mut HashSet<usize>,
        ends: &mut HashSet<usize>,
    ) {
        if matches!(node.kind(), "namespace" | "verification") {
            ends.insert(node.end_byte());
            for child in node.children(&mut node.walk()) {
                match child.kind() {
                    "{" => {
                        opens.insert(child.start_byte());
                    }
                    "}" => {
                        closes.insert(child.start_byte());
                    }
                    _ => {}
                }
            }
        }
        for child in node.named_children(&mut node.walk()) {
            blocks(child, opens, closes, ends);
        }
    }
    let (mut opens, mut closes, mut ends) = (HashSet::new(), HashSet::new(), HashSet::new());
    blocks(doc.tree.root_node(), &mut opens, &mut closes, &mut ends);
    let mut indent = 0usize;
    let mut depth = 0usize;
    let mut body = false;
    let mut previous: Option<&Lexeme> = None;
    for token in &tokens {
        let at = &source[token.start..token.end];
        let start = previous.map_or(0, |p| p.end);
        let old = &source[start..token.start];
        let prev = previous.map_or("", |p| &source[p.start..p.end]);
        if closes.contains(&token.start) {
            indent = indent.saturating_sub(1);
        }
        let newline = || {
            let eols = endings(old);
            format!(
                "{}{}",
                if eols.is_empty() {
                    default_eol.to_owned()
                } else {
                    eols.concat()
                },
                "    ".repeat(indent + usize::from(body))
            )
        };
        let desired = if token.kind == "comment" {
            old.to_owned()
        } else if previous.is_some_and(|p| p.kind == "comment") {
            newline()
        } else if previous.is_none() {
            String::new()
        } else if closes.contains(&token.start)
            || previous.is_some_and(|p| opens.contains(&p.start) || ends.contains(&p.end))
        {
            newline()
        } else if prev == ";" {
            newline()
        } else if prev == ":-" || (prev == "," && depth == 0 && body) {
            newline()
        } else if matches!(at, "(" | ")" | "," | ";" | ":" | "]")
            || matches!(prev, "(" | "!" | "[" | "::" | "#" | "$")
            || (at == "::"
                && !denotate_ir_text::reserved_word(prev)
                && previous.is_some_and(|p| matches!(p.kind, "identifier" | "quoted")))
        {
            String::new()
        } else {
            " ".into()
        };
        let range = Range::new(doc.position(start), doc.position(token.start));
        let selected = selection.is_none_or(|s| s.start <= range.start && range.end <= s.end);
        if desired != old
            && old.chars().all(whitespace)
            && selected
            && !(range.start.line..=range.end.line).any(|line| damaged.contains(&line))
        {
            edits.push((start, token.start, desired));
        }
        if token.kind != "comment" {
            match at {
                "(" => depth += 1,
                ")" => depth = depth.saturating_sub(1),
                ":-" => body = true,
                ";" => {
                    body = false;
                    depth = 0;
                }
                _ => {}
            }
        }
        if opens.contains(&token.start) {
            indent += 1;
        }
        previous = Some(token);
    }
    let mut formatted = source.clone();
    for (start, end, text) in edits.iter().rev() {
        formatted.replace_range(*start..*end, text);
    }
    // Re-lex the actual resulting text, never just the recovered CST. Comments,
    // unknown characters and attachment are part of the invariant.
    if fingerprint(source) != fingerprint(&formatted) {
        return json!([]);
    }
    json!(edits.into_iter().map(|(start,end,text)| json!({"range": Range::new(doc.position(start), doc.position(end)), "newText": text})).collect::<Vec<_>>())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verification_blocks_format_with_quoted_names_comments_and_attached_origins() {
        let source = "namespace lib{notice n:varies(g,within:p);verification 'check me'{assumptions:[::'a::b'::allowed, ::other];obligations:[unique];notices:[n];}loc(#origin)\nverification empty{assumptions:[];obligations:[];}\n}\n";
        let expected = "namespace lib {\n    notice n: varies(g, within: p);\n    verification 'check me' {\n        assumptions: [::'a::b'::allowed, ::other];\n        obligations: [unique];\n        notices: [n];\n    } loc(#origin)\n    verification empty {\n        assumptions: [];\n        obligations: [];\n    }\n}\n";
        for (source, expected) in [
            (source.to_string(), expected.to_string()),
            (source.replace('\n', "\r\n"), expected.replace('\n', "\r\n")),
        ] {
            let mut parser = crate::syntax::parser();
            let doc = Document::new(&mut parser, source.clone(), 1, true);
            assert!(doc.diagnostics().is_empty());
            let mut formatted = source.clone();
            for edit in format(&doc, None).as_array().unwrap().iter().rev() {
                let range: Range = serde_json::from_value(edit["range"].clone()).unwrap();
                formatted.replace_range(
                    doc.offset(range.start).unwrap()..doc.offset(range.end).unwrap(),
                    edit["newText"].as_str().unwrap(),
                );
            }
            assert_eq!(formatted, expected);
            assert_eq!(fingerprint(&source), fingerprint(&formatted));
            let second = Document::new(&mut parser, formatted, 2, true);
            assert!(second.diagnostics().is_empty());
            assert_eq!(format(&second, None), json!([]));
        }
        let mut parser = crate::syntax::parser();
        for source in [
            "verification v { // keep this comment attached\n assumptions: [a]; // selected assumption\n obligations: [];\n}",
            "verification broken { assumptions: [a, ; obligations: []; }",
            "verification v { assumptions: []; obligations: []; } loc(#s {self: 12:34 to 56:78})",
        ] {
            let doc = Document::new(&mut parser, source.into(), 1, true);
            let mut formatted = source.to_owned();
            for edit in format(&doc, None).as_array().unwrap().iter().rev() {
                let range: Range = serde_json::from_value(edit["range"].clone()).unwrap();
                formatted.replace_range(doc.offset(range.start).unwrap()..doc.offset(range.end).unwrap(), edit["newText"].as_str().unwrap());
            }
            assert_eq!(fingerprint(source), fingerprint(&formatted));
            let second = Document::new(&mut parser, formatted, 2, true);
            assert_eq!(format(&second, None), json!([]));
        }
    }

    #[test]
    fn every_fixture_preserves_tokens_and_is_idempotent_with_useful_coverage() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures");
        let manifest: Value =
            serde_json::from_str(&std::fs::read_to_string(root.join("syntax.json")).unwrap())
                .unwrap();
        let mut parser = crate::syntax::parser();
        let mut changed = 0;
        for case in manifest["cases"].as_array().unwrap() {
            let file = case["file"].as_str().unwrap();
            let source = std::fs::read_to_string(root.join(file)).unwrap();
            let doc = Document::new(&mut parser, source.clone(), 1, true);
            let edits = format(&doc, None);
            let mut formatted = source.clone();
            for edit in edits.as_array().unwrap().iter().rev() {
                let range: Range = serde_json::from_value(edit["range"].clone()).unwrap();
                formatted.replace_range(
                    doc.offset(range.start).unwrap()..doc.offset(range.end).unwrap(),
                    edit["newText"].as_str().unwrap(),
                );
            }
            assert_eq!(fingerprint(&source), fingerprint(&formatted), "{file}");
            if source != formatted {
                changed += 1;
            }
            if file == "base/00-valid/computation.den" {
                assert_ne!(source, formatted, "must format short rule bodies");
            }
            let second = Document::new(&mut parser, formatted, 2, true);
            assert_eq!(format(&second, None), json!([]), "{file}");
        }
        assert!(changed > 0);
        println!(
            "B formatter changes {changed}/{} fixtures",
            manifest["cases"].as_array().unwrap().len()
        );
    }
}
