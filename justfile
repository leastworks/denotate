# Show the available commands.
default:
    @just --list

# Test Rust/Salsa analysis, IR, concrete checking, the test DSL and instrumentation.
test-crates:
    cargo +1.93.0 test --locked --workspace --exclude denotate-lsp --exclude denotate-lsp-tests

# Re-score retained slice-6 paths on a program: FILE [--edit FILE] [--samples N] [--json FILE].
[positional-arguments]
score-inputmapping +args:
    cargo +1.93.0 run --release --locked -p denotate-check-session --features test-support --example scorecard -- "$@"

# Export one combined InputMapping program: OUT_DIR FILE... [--without-origins].
[positional-arguments]
export-inputmapping +args:
    cargo +1.93.0 run --locked -p denotate-test-dsl --example export -- "$@"

# Load and check a folder-rooted .den program: ROOT_FOLDER_OR_DEN.ROOT [--sat].
[positional-arguments]
check-den +args:
    cargo +1.93.0 run --locked -p denotate-ir-text --example check -- "$@"

# Source-linked InputMapping findings; also try mixed, requires-c or fixed.
demo-overlap mode="overlap":
    cargo +1.93.0 run --locked -p denotate-test-dsl --example overlap -- {{mode}}

# Parse actual InputMapping text and lower it to IR; no semantic checking or editor.
parse-inputmapping file="test-dsl/fixtures/overlapping-mappings.txt":
    cargo +1.93.0 run --locked -p denotate-test-dsl --example parse -- '{{file}}'

# Rewrite the InputMapping corpus expectations from current behavior; review the diff.
update-inputmapping-expectations:
    UPDATE_EXPECTATIONS=1 cargo +1.93.0 test --locked -p denotate-test-dsl --lib corpus_programs_match_their_expectations

# Regenerate the committed DSL parser with the .den editor's pinned CLI (npm ci there first).
generate-inputmapping: _check-node
    cd test-dsl/grammar && ../../den/lsp/node_modules/.bin/tree-sitter generate

# Build the InputMapping diagnostics server and exercise it over real LSP (no GUI).
test-inputmapping-lsp:
    cargo +1.93.0 build --locked -p denotate-test-dsl --bin inputmapping-lsp
    DENOTATE_LSP_COMMAND="{{justfile_directory()}}/target/debug/inputmapping-lsp" DENOTATE_LSP_ARGS='[]' cargo +1.93.0 test --locked -p denotate-lsp-tests --features inputmapping --test inputmapping

# Build the InputMapping VS Code extension and check its package/example (no GUI).
test-inputmapping-extension: _check-node
    npm test --prefix test-dsl/vscode

# Launch an isolated VS Code and test source-linked InputMapping diagnostics.
test-inputmapping-vscode: _check-node
    DENOTATE_VSCODE_EXECUTABLE="${DENOTATE_VSCODE_EXECUTABLE:-/Applications/Visual Studio Code.app/Contents/MacOS/Code}" npm run test:vscode --prefix test-dsl/vscode

# Build the .den editor, check the shared syntax manifest and run every shared LSP scenario.
test-b: _check-node
    npm test --prefix den/lsp
    npm run test:lsp --prefix den/lsp

# Launch an isolated VS Code with the .den editor extension under test.
test-b-vscode: _check-node
    DENOTATE_VSCODE_EXECUTABLE="${DENOTATE_VSCODE_EXECUTABLE:-/Applications/Visual Studio Code.app/Contents/MacOS/Code}" npm run test:vscode --prefix den/lsp

# Measure real .den LSP round trips at three sizes; no timing pass/fail threshold.
bench-lsp: _check-node
    npm run build --prefix den/lsp
    cargo +1.93.0 test --locked -p denotate-lsp-tests --test latency -- --ignored --nocapture --test-threads=1

[private]
_check-node:
    @node -e 'if (Number(process.versions.node.split(".")[0]) < 22) { console.error("Denotate needs Node 22+. Check node --version and your PATH."); process.exit(1); }'
