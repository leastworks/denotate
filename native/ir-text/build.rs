fn main() {
    let grammar = "../../tree-sitter/grammar/src";
    println!("cargo:rerun-if-changed={grammar}/parser.c");
    println!("cargo:rerun-if-changed={grammar}/tree_sitter/parser.h");
    cc::Build::new()
        .include(grammar)
        .file(format!("{grammar}/parser.c"))
        .warnings(false)
        .compile("tree-sitter-denotate");
}
