fn main() {
    println!("cargo:rerun-if-changed=../../grammars/test-dsl/src/parser.c");
    println!("cargo:rerun-if-changed=../../grammars/test-dsl/src/tree_sitter/parser.h");
    cc::Build::new()
        .include("../../grammars/test-dsl/src")
        .file("../../grammars/test-dsl/src/parser.c")
        .warnings(false)
        .compile("tree-sitter-testdsl");
}
