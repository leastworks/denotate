# Show the available commands.
default:
    @just --list

# Test Rust/Salsa analysis, IR, concrete checking, the test DSL and instrumentation.
test-crates:
    cargo +1.93.0 test --locked --workspace --exclude denotate-lsp --exclude denotate-lsp-tests

# Re-score retained slice-6 paths on a program: FILE [--edit FILE] [--samples N] [--json FILE].
[positional-arguments]
score-test-dsl +args:
    cargo +1.93.0 run --release --locked -p denotate-check-session --features test-support --example scorecard -- "$@"

# Export one combined test DSL program: OUT_DIR FILE... [--without-origins].
[positional-arguments]
export-test-dsl +args:
    cargo +1.93.0 run --locked -p denotate-test-dsl --example export -- "$@"

# Load and check a folder-rooted .den program: ROOT_FOLDER_OR_DEN.ROOT.
[positional-arguments]
check-den +args:
    cargo +1.93.0 run --locked -p denotate-ir-text --example check -- "$@"

# Source-linked test DSL findings; also try mixed, requires-c or fixed.
demo-overlap mode="overlap":
    cargo +1.93.0 run --locked -p denotate-test-dsl --example overlap -- {{mode}}

# Parse actual test DSL text and lower it to IR; no semantic checking or editor.
parse-test-dsl file="crates/test-dsl/fixtures/overlapping-mappings.txt":
    cargo +1.93.0 run --locked -p denotate-test-dsl --example parse -- '{{file}}'

# Rewrite the test DSL corpus expectations from current behavior; review the diff.
update-test-dsl-expectations:
    UPDATE_EXPECTATIONS=1 cargo +1.93.0 test --locked -p denotate-test-dsl --lib corpus_programs_match_their_expectations

# Regenerate the committed DSL parser with the .den editor's pinned CLI (npm ci there first).
generate-test-dsl: _check-node
    cd grammars/test-dsl && ../../editors/den/node_modules/.bin/tree-sitter generate

# Build the test DSL diagnostics server and exercise it over real LSP (no GUI).
test-dsl-lsp:
    cargo +1.93.0 build --locked -p denotate-test-dsl --bin test-dsl-lsp
    DENOTATE_LSP_COMMAND="{{justfile_directory()}}/target/debug/test-dsl-lsp" DENOTATE_LSP_ARGS='[]' cargo +1.93.0 test --locked -p denotate-lsp-tests --features test-dsl --test test_dsl

# Build the test DSL VS Code extension and check its package/example (no GUI).
test-dsl-extension: _check-node
    npm test --prefix editors/test-dsl

# Launch an isolated VS Code and test source-linked test DSL diagnostics.
test-dsl-vscode: _check-node
    DENOTATE_VSCODE_EXECUTABLE="${DENOTATE_VSCODE_EXECUTABLE:-/Applications/Visual Studio Code.app/Contents/MacOS/Code}" npm run test:vscode --prefix editors/test-dsl

# Build the .den editor, check the shared syntax manifest and run every shared LSP scenario.
test-den: _check-node
    npm test --prefix editors/den
    npm run test:lsp --prefix editors/den

# Launch an isolated VS Code with the .den editor extension under test.
test-den-vscode: _check-node
    DENOTATE_VSCODE_EXECUTABLE="${DENOTATE_VSCODE_EXECUTABLE:-/Applications/Visual Studio Code.app/Contents/MacOS/Code}" npm run test:vscode --prefix editors/den

# Measure real .den LSP round trips at three sizes; no timing pass/fail threshold.
bench-lsp: _check-node
    npm run build --prefix editors/den
    cargo +1.93.0 test --locked -p denotate-lsp-tests --test latency -- --ignored --nocapture --test-threads=1

[private]
_check-node:
    @node -e 'if (Number(process.versions.node.split(".")[0]) < 22) { console.error("Denotate needs Node 22+. Check node --version and your PATH."); process.exit(1); }'
