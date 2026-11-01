# Show the available commands.
default:
    @just --list

# Prepare the pinned Rust toolchain and both editors' dependencies.
setup: setup-den setup-test-dsl
    rustup toolchain install 1.93.0 --profile minimal --component rustfmt

# Install .den editor dependencies only when missing or changed; --force reinstalls.
[positional-arguments]
setup-den *args: _check-node
    @node scripts/ensure-editor-deps.mjs den "$@"

# Install test DSL editor dependencies only when missing or changed; --force reinstalls.
[positional-arguments]
setup-test-dsl *args: _check-node
    @node scripts/ensure-editor-deps.mjs test-dsl "$@"

# Build the .den server and VS Code client; prepares dependencies automatically.
build-den:
    npm run build --prefix editors/den

# Build the test DSL server and VS Code client; prepares dependencies automatically.
build-test-dsl:
    npm run build --prefix editors/test-dsl

# Run one Rust crate's tests; accepts additional Cargo test arguments.
[positional-arguments]
test-crate crate *args:
    cargo +1.93.0 test --locked -p "$@"

# Check setup/install caching without downloading dependencies.
test-tooling: _check-node
    node --test scripts/tests/*.test.mjs

# Check every Shipping News lesson and exercise.
test-shipping-news:
    cargo +1.93.0 test --locked -p denotate-ir-text --example check shipping_news

# Check the .den scorecard.
test-score-den:
    cargo +1.93.0 test --release --locked -p denotate-check-session --features test-support --example score_den

# Check the test DSL scorecard.
test-score-test-dsl:
    cargo +1.93.0 test --release --locked -p denotate-check-session --features test-support --example scorecard

# Check both scorecards (release builds; not part of `verify`).
test-scorecards: test-score-den test-score-test-dsl

# Format all Rust crates.
fmt:
    cargo +1.93.0 fmt --all

# Check formatting without changing files.
fmt-check:
    cargo +1.93.0 fmt --all --check

# Run the verification gate without launching VS Code.
verify: test-crates test-den test-dsl-lsp test-dsl-extension fmt-check

# Run the installed VS Code smokes, one after the other.
verify-vscode: test-den-vscode test-dsl-vscode

# Test Rust/Salsa analysis, IR, concrete checking, the test DSL and instrumentation.
test-crates:
    cargo +1.93.0 test --locked --workspace --exclude denotate-lsp --exclude denotate-lsp-tests

# Re-score retained slice-6 paths on a program: FILE [--edit FILE] [--samples N] [--json FILE].
[positional-arguments]
score-test-dsl +args:
    cargo +1.93.0 run --release --locked -p denotate-check-session --features test-support --example scorecard -- "$@"

# Re-score explicit .den verifications: ROOT [--edit ROOT] [--samples N] [--json FILE].
[positional-arguments]
score-den +args:
    cargo +1.93.0 run --release --locked -p denotate-check-session --features test-support --example score_den -- "$@"

# Export one combined test DSL program: OUT_DIR FILE... [--without-origins].
[positional-arguments]
export-test-dsl +args:
    cargo +1.93.0 run --locked -p denotate-test-dsl --example export -- "$@"

# Build the .den editor and open FOLDER (relative to where you run just) in VS Code with it.
[positional-arguments]
edit-den folder: build-den
    code --extensionDevelopmentPath="{{justfile_directory()}}/editors/den" "$(cd "{{invocation_directory()}}" && cd "$1" && pwd)"

# Build the test DSL editor and open FOLDER in VS Code with it.
[positional-arguments]
edit-test-dsl folder: build-test-dsl
    code --extensionDevelopmentPath="{{justfile_directory()}}/editors/test-dsl" "$(cd "{{invocation_directory()}}" && cd "$1" && pwd)"

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

# Generate the .den parser only if needed; --force bypasses its local cache.
[positional-arguments]
generate-den *args: setup-den
    npm run generate --prefix editors/den -- "$@"

# Test .den parser generation caching and recovery.
test-den-generation: setup-den
    npm run test:generation --prefix editors/den

# Test Go to Origin navigation without launching VS Code.
test-den-origins: setup-den
    npm run test:origins --prefix editors/den

# Regenerate the committed test DSL parser with the pinned CLI.
generate-test-dsl: setup-den
    cd grammars/test-dsl && ../../editors/den/node_modules/.bin/tree-sitter generate

# Build the test DSL diagnostics server and exercise it over real LSP (no GUI).
test-dsl-lsp:
    cargo +1.93.0 build --locked -p denotate-test-dsl --bin test-dsl-lsp
    DENOTATE_LSP_COMMAND="{{justfile_directory()}}/target/debug/test-dsl-lsp" DENOTATE_LSP_ARGS='[]' cargo +1.93.0 test --locked -p denotate-lsp-tests --features test-dsl --test test_dsl

# Build the test DSL VS Code extension and check its package/example (no GUI).
test-dsl-extension:
    npm test --prefix editors/test-dsl

# Launch an isolated VS Code and test source-linked test DSL diagnostics.
test-dsl-vscode:
    DENOTATE_VSCODE_EXECUTABLE="${DENOTATE_VSCODE_EXECUTABLE:-/Applications/Visual Studio Code.app/Contents/MacOS/Code}" npm run test:vscode --prefix editors/test-dsl

# Build the .den editor, check the shared syntax manifest and run every shared LSP scenario.
test-den: setup-den
    npm test --prefix editors/den
    npm run test:lsp --prefix editors/den

# Launch an isolated VS Code with the .den editor extension under test.
test-den-vscode:
    DENOTATE_VSCODE_EXECUTABLE="${DENOTATE_VSCODE_EXECUTABLE:-/Applications/Visual Studio Code.app/Contents/MacOS/Code}" npm run test:vscode --prefix editors/den

# Measure real .den LSP round trips at three sizes; no timing pass/fail threshold.
bench-lsp:
    npm run build --prefix editors/den
    cargo +1.93.0 test --locked -p denotate-lsp-tests --test latency -- --ignored --nocapture --test-threads=1

[private]
_check-node:
    @node -e 'if (Number(process.versions.node.split(".")[0]) < 22) { console.error("Denotate needs Node 22+. Check node --version and your PATH."); process.exit(1); }'
