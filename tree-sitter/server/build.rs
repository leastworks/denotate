fn main() {
    println!("cargo:rerun-if-changed=../grammar/src/parser.c");
    println!("cargo:rerun-if-changed=../grammar/src/tree_sitter/parser.h");
    cc::Build::new()
        .include("../grammar/src")
        .file("../grammar/src/parser.c")
        .warnings(false)
        .compile("tree-sitter-denotate");
}
