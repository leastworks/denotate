import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
const root = fileURLToPath(new URL('../../', import.meta.url));
const server = fileURLToPath(new URL(`../dist/denotate-lsp${process.platform === 'win32' ? '.exe' : ''}`, import.meta.url));
const env = { ...process.env, DENOTATE_BACKEND: 'tree-sitter', DENOTATE_LSP_COMMAND: server, DENOTATE_LSP_ARGS: '[]' };
// B3 editor parity; lifecycle/cancellation and profiling remain B4/B5.
for (const [binary, filter] of [
    ['b1'], ['b2'], ['editor'], ['resolution'], ['rename'], ['formatting'],
    ['deferred'], ['rules'], ['acceptance'], ['a2']
]) {
    const result = spawnSync('cargo', ['test', '--manifest-path', `${root}Cargo.toml`, '--locked',
        '-p', 'denotate-lsp-tests', '--test', binary, ...(filter ? [filter] : []), '--', '--nocapture'], { env, stdio: 'inherit' });
    if (result.error) throw result.error;
    if (result.status !== 0) process.exit(result.status ?? 1);
}
