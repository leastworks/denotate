# Show the available commands.
default:
    @just --list

# Build and run the Denotate parser + fixture checks (no editor window).
test-parser: _check-node
    npm test --prefix frontend-prototype/langium

# Build the server and run the Rust tests against it over LSP.
test-lsp: _check-node
    npm run build --prefix frontend-prototype/langium
    cargo test --manifest-path frontend-prototype/Cargo.toml --locked -p denotate-lsp-tests

# Measure real LSP round trips at three sizes; no timing pass/fail threshold.
bench-lsp: _check-node
    npm run build --prefix frontend-prototype/langium
    cargo test --manifest-path frontend-prototype/Cargo.toml --locked -p denotate-lsp-tests --test latency -- --ignored --nocapture --test-threads=1

# Launch an isolated VS Code, smoke-test the extension, then close it.
test-vscode: _check-node
    DENOTATE_VSCODE_EXECUTABLE="${DENOTATE_VSCODE_EXECUTABLE:-/Applications/Visual Studio Code.app/Contents/MacOS/Code}" npm run test:vscode --prefix frontend-prototype/langium

[private]
_check-node:
    @node -e 'if (Number(process.versions.node.split(".")[0]) < 22) { console.error("Denotate needs Node 22+. Check node --version and your PATH."); process.exit(1); }'
