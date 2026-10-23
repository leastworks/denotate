# Show the available commands.
default:
    @just --list

# Build and run the Denotate parser + fixture checks (no editor window).
test-parser: _check-node
    npm test --prefix frontend-prototype/langium

# Build the server and run the Rust tests against it over LSP.
test-lsp: _check-node
    cargo run --manifest-path frontend-prototype/Cargo.toml --locked -p xtask -- test-lsp

# Test Rust/Salsa analysis, IR, concrete checking, the test DSL and instrumentation.
test-native:
    cargo +1.93.0 test --manifest-path frontend-prototype/native/Cargo.toml --locked --workspace --exclude denotate-tree-sitter

# Re-score retained slice-6 paths on a program: FILE [--edit FILE] [--samples N] [--json FILE].
[positional-arguments]
score-inputmapping +args:
    cargo +1.93.0 run --release --manifest-path frontend-prototype/native/Cargo.toml --locked -p denotate-check-session --features test-support --example scorecard -- "$@"

# Load and check a folder-rooted .den program: ROOT_FOLDER_OR_DEN.ROOT [--sat].
[positional-arguments]
check-den +args:
    cargo +1.93.0 run --manifest-path frontend-prototype/native/Cargo.toml --locked -p denotate-ir-text --example check -- "$@"

# Source-linked InputMapping findings; also try mixed, requires-c or fixed.
demo-overlap mode="overlap":
    cargo +1.93.0 run --manifest-path frontend-prototype/native/Cargo.toml --locked -p denotate-test-dsl --example overlap -- {{mode}}

# Parse actual InputMapping text and lower it to IR; no semantic checking or editor.
parse-inputmapping file="frontend-prototype/native/test-dsl/fixtures/overlapping-mappings.txt":
    cargo +1.93.0 run --manifest-path frontend-prototype/native/Cargo.toml --locked -p denotate-test-dsl --example parse -- '{{file}}'

# Regenerate the committed DSL parser with B's pinned CLI (npm ci there first).
generate-inputmapping: _check-node
    cd frontend-prototype/native/test-dsl/grammar && ../../../tree-sitter/node_modules/.bin/tree-sitter generate

# Build the InputMapping diagnostics server and exercise it over real LSP (no GUI).
test-inputmapping-lsp:
    cargo +1.93.0 build --manifest-path frontend-prototype/native/Cargo.toml --locked -p denotate-test-dsl --bin inputmapping-lsp
    DENOTATE_LSP_COMMAND="{{justfile_directory()}}/frontend-prototype/native/target/debug/inputmapping-lsp" DENOTATE_LSP_ARGS='[]' cargo +1.78.0 test --manifest-path frontend-prototype/Cargo.toml --locked -p denotate-lsp-tests --features inputmapping --test inputmapping

# Measure cold/comment-edit lowering phases and full checking through LSP.
bench-inputmapping-lowering:
    cargo +1.93.0 build --manifest-path frontend-prototype/native/Cargo.toml --locked -p denotate-test-dsl --bin inputmapping-lsp --release
    DENOTATE_LSP_COMMAND="{{justfile_directory()}}/frontend-prototype/native/target/release/inputmapping-lsp" DENOTATE_LSP_ARGS='[]' cargo +1.78.0 test --manifest-path frontend-prototype/Cargo.toml --locked -p denotate-lsp-tests --features inputmapping --test inputmapping measure_cached_lowering_phases -- --ignored --nocapture --test-threads=1

# Compare cold/comment-edit phases with zero masks or conditional masks on half the Slots.
bench-inputmapping-masking:
    cargo +1.93.0 build --manifest-path frontend-prototype/native/Cargo.toml --locked -p denotate-test-dsl --bin inputmapping-lsp --release
    DENOTATE_LSP_COMMAND="{{justfile_directory()}}/frontend-prototype/native/target/release/inputmapping-lsp" DENOTATE_LSP_ARGS='[]' cargo +1.78.0 test --manifest-path frontend-prototype/Cargo.toml --locked -p denotate-lsp-tests --features inputmapping --test inputmapping measure_masking_phases -- --ignored --nocapture --test-threads=1

# Build the InputMapping VS Code extension and check its package/example (no GUI).
test-inputmapping-extension: _check-node
    npm test --prefix frontend-prototype/native/test-dsl/vscode

# Launch an isolated VS Code and test source-linked InputMapping diagnostics.
test-inputmapping-vscode: _check-node
    DENOTATE_VSCODE_EXECUTABLE="${DENOTATE_VSCODE_EXECUTABLE:-/Applications/Visual Studio Code.app/Contents/MacOS/Code}" npm run test:vscode --prefix frontend-prototype/native/test-dsl/vscode

# Optional independent Python/Z3 check of four Rust fixture corpora (needs z3-solver).
test-check-z3:
    python3 semantics/check_rust_findings.py

# Build B, check the shared syntax manifest and run its supported LSP scenarios.
test-b: _check-node
    npm test --prefix frontend-prototype/tree-sitter
    npm run test:lsp --prefix frontend-prototype/tree-sitter

# Launch an isolated VS Code with only the Tree-sitter prototype under test.
test-b-vscode: _check-node
    DENOTATE_VSCODE_EXECUTABLE="${DENOTATE_VSCODE_EXECUTABLE:-/Applications/Visual Studio Code.app/Contents/MacOS/Code}" npm run test:vscode --prefix frontend-prototype/tree-sitter

# Run the retained A1 frontend without loading or building the native extension.
test-a1: _check-node
    DENOTATE_BACKEND=langium cargo run --manifest-path frontend-prototype/Cargo.toml --locked -p xtask -- test-lsp

# Measure real LSP round trips at three sizes; no timing pass/fail threshold.
bench-lsp: _check-node
    npm run build --prefix frontend-prototype/langium
    cargo test --manifest-path frontend-prototype/Cargo.toml --locked -p denotate-lsp-tests --test latency -- --ignored --nocapture --test-threads=1

# Profile projection, boundary and Rust costs for cold/comment/semantic edits.
profile-lsp: _check-node
    npm run build --prefix frontend-prototype/langium
    cargo test --manifest-path frontend-prototype/Cargo.toml --locked -p denotate-lsp-tests --test profiling -- --ignored --nocapture --test-threads=1

# Rebuild and compare A2/B latency and pipeline costs in three alternating runs.
compare-frontends: _check-node
    node frontend-prototype/measure/compare.mjs

# Launch an isolated VS Code, smoke-test the extension, then close it.
test-vscode: _check-node
    DENOTATE_VSCODE_EXECUTABLE="${DENOTATE_VSCODE_EXECUTABLE:-/Applications/Visual Studio Code.app/Contents/MacOS/Code}" npm run test:vscode --prefix frontend-prototype/langium

[private]
_check-node:
    @node -e 'if (Number(process.versions.node.split(".")[0]) < 22) { console.error("Denotate needs Node 22+. Check node --version and your PATH."); process.exit(1); }'
