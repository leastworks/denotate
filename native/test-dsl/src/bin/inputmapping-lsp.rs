#[path = "../server/mod.rs"]
mod server;

fn main() {
    if let Err(error) = denotate_editor::transport::stdio(server::run) {
        eprintln!("InputMapping server: {error}");
        std::process::exit(1);
    }
}
