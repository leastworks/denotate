#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use support::apply_edits;

fn edit(start: (u32, u32), end: (u32, u32), new_text: &str) -> Value {
    json!({"range":{"start":{"line":start.0,"character":start.1},
        "end":{"line":end.0,"character":end.1}},"newText":new_text})
}

#[test]
fn applies_unsorted_edits_using_original_utf16_positions_and_preserves_line_endings() {
    let text = "é😀 alpha\r\nsecond\rthird\n";
    let edits = [
        edit((2, 0), (2, 5), "last"),
        edit((0, 4), (0, 9), "longer_name"),
        edit((3, 0), (3, 0), "end"),
        edit((1, 0), (1, 6), ""),
    ];
    assert_eq!(apply_edits(text, &edits), "é😀 longer_name\r\n\rlast\nend");
    assert_eq!(apply_edits(text, &[]), text);
    assert_eq!(apply_edits("", &[edit((0, 0), (0, 0), "new")]), "new");
    assert_eq!(apply_edits("a\r\nb", &[edit((0, 1), (1, 0), " ")]), "a b");
    assert_eq!(
        apply_edits("x", &[edit((0, 0), (0, 0), "a"), edit((0, 0), (0, 0), "b")]),
        "abx"
    );
}

#[test]
fn rejects_invalid_utf16_positions_reversed_ranges_and_overlaps() {
    for edits in [
        vec![edit((0, 1), (0, 2), "x")], // inside the emoji's surrogate pair
        vec![edit((1, 0), (1, 0), "x")], // nonexistent line
        vec![edit((0, 99), (0, 99), "x")], // beyond line end
        vec![edit((0, 3), (0, 2), "x")],
        vec![edit((0, 0), (0, 3), "x"), edit((0, 2), (0, 4), "y")],
    ] {
        assert!(std::panic::catch_unwind(|| apply_edits("😀ab", &edits)).is_err());
    }
}
