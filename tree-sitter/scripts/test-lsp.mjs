import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
const root = fileURLToPath(new URL('../../', import.meta.url));
const server = fileURLToPath(new URL(`../dist/denotate-lsp${process.platform === 'win32' ? '.exe' : ''}`, import.meta.url));
// Run every shared LSP scenario against the freshly built .den server. The
// InputMapping scenarios are feature-gated and run through their own recipe.
const env = { ...process.env, DENOTATE_LSP_COMMAND: server, DENOTATE_LSP_ARGS: '[]' };
const result = spawnSync('cargo', ['test', '--manifest-path', `${root}Cargo.toml`, '--locked',
    '-p', 'denotate-lsp-tests', '--', '--nocapture'], { env, stdio: 'inherit' });
if (result.error) throw result.error;
process.exit(result.status ?? 1);
