import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
const root = fileURLToPath(new URL('../../', import.meta.url));
const server = fileURLToPath(new URL(`../dist/denotate-lsp${process.platform === 'win32' ? '.exe' : ''}`, import.meta.url));
const env = { ...process.env, DENOTATE_BACKEND: 'tree-sitter', DENOTATE_LSP_COMMAND: server, DENOTATE_LSP_ARGS: '[]' };
// Explicit B1 subset: never count absent semantic/editor capabilities as passes.
for (const [binary, filter] of [
    ['b1'], ['editor', 'unopened_bom_file_uses_editor_columns'],
    ['editor', 'standalone_unicode_comment_shifts_outline_lines'],
    ['editor', 'damaged_library_does_not_prevent_importer_syntax_outline']
]) {
    const result = spawnSync('cargo', ['test', '--manifest-path', `${root}Cargo.toml`, '--locked',
        '-p', 'denotate-lsp-tests', '--test', binary, ...(filter ? [filter] : [])], { env, stdio: 'inherit' });
    if (result.error) throw result.error;
    if (result.status !== 0) process.exit(result.status ?? 1);
}
