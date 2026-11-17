fn git(args: &[&str]) -> Option<String> {
    std::process::Command::new("git")
        .args(args)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_owned())
}
fn watch(path: &str) {
    let mut path = std::path::PathBuf::from(path);
    // Packed branches have no loose ref file. Watching a nonexistent path would
    // rerun this script on every build; watch its nearest existing parent instead.
    while !path.exists() {
        if !path.pop() {
            return;
        }
    }
    println!("cargo:rerun-if-changed={}", path.display());
}
fn main() {
    // Stamp the build's base revision. Do not watch the index (git status can
    // refresh it) or rebuild the C parser for ordinary Rust/source edits.
    if let Some(head) = git(&["rev-parse", "--git-path", "HEAD"]) {
        watch(&head);
        if let Ok(text) = std::fs::read_to_string(head) {
            if let Some(reference) = text.trim().strip_prefix("ref: ") {
                if let Some(path) = git(&["rev-parse", "--git-path", reference]) {
                    watch(&path);
                }
            }
        }
    }
    if let Some(path) = git(&["rev-parse", "--git-path", "packed-refs"]) {
        if std::path::Path::new(&path).exists() {
            watch(&path);
        }
    }
    let commit = git(&["rev-parse", "HEAD"]).unwrap_or_else(|| "unknown-source-archive".into());
    println!("cargo:rustc-env=DENOTATE_CHECKER_COMMIT={commit}");
    let grammar = "../../grammars/den/src";
    println!("cargo:rerun-if-changed={grammar}/parser.c");
    println!("cargo:rerun-if-changed={grammar}/tree_sitter/parser.h");
    cc::Build::new()
        .include(grammar)
        .file(format!("{grammar}/parser.c"))
        .warnings(false)
        .compile("tree-sitter-denotate");
}
