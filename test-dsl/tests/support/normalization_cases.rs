// Generated normalization cases: nested Boolean shapes plus duplicate and moved statements.
pub fn nested() -> Vec<String> {
    let mut texts = vec![];
    let leaves = [
        "present(i)",
        "available(a)",
        "not present(j)",
        "not not (available(b))",
    ];
    for a in leaves {
        for b in leaves {
            for shape in [
                format!("not (({a}) or ({b}))"),
                format!("not (({a}) and ({b}))"),
                format!("not (not (({a}) or ({b})))"),
                format!("({a}) and (({b}) or not ({a}))"),
                format!("not (not (({a}) and ({b})))"),
            ] {
                texts.push(format!(
                    "input i, j; slot a, b; a <- i when {shape}; mask b when {shape};"
                ));
            }
        }
    }
    texts
}
pub const DUPLICATES: &str = "input i, j; slot a, b; a <- i when not (available(b) and present(j)); a <- i when not (available(b) and present(j)); mask b when not present(j);";
pub fn moved() -> [(u64, String); 2] {
    [
        (2, format!("// moved\n{DUPLICATES}")),
        (3, DUPLICATES.replace("not present(j)", "not    present(j)")),
    ]
}
pub fn capture_cases() -> Vec<(u64, String)> {
    nested()
        .into_iter()
        .map(|t| (1, t))
        .chain(std::iter::once((1, DUPLICATES.to_owned())))
        .chain(moved())
        .chain(std::iter::once((
            4,
            DUPLICATES.replace("present(j)", "present(i)"),
        )))
        .collect()
}
