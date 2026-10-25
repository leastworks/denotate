use denotate_test_dsl::server;

fn main() {
    if let Err(error) = denotate_editor::transport::stdio(server::run) {
        eprintln!("test DSL server: {error}");
        std::process::exit(1);
    }
}
