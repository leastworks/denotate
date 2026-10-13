# Show the available commands.
default:
    @just --list

# Build and run the Denotate parser + fixture checks (no editor window).
test-parser: _check-node
    npm test --prefix frontend-prototype/langium

# Build the server and run the Rust tests against it over LSP.
test-lsp: _check-node
    cargo run --manifest-path frontend-prototype/Cargo.toml --locked -p xtask -- test-lsp

# Test Rust/Salsa analysis, IR construction, the test DSL and native instrumentation.
test-native:
    cargo +1.93.0 test --manifest-path frontend-prototype/native/Cargo.toml --locked --workspace --exclude denotate-tree-sitter

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
