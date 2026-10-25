import { build } from 'esbuild';
import { chmod, copyFile, mkdir, rm } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('.', import.meta.url));
await mkdir(new URL('dist/', import.meta.url), { recursive: true });
for (const [entry, output] of [
    ['src/extension.cjs', 'dist/extension.cjs'],
    ['tests/vscode-smoke.cjs', 'dist/vscode-smoke.cjs']
]) {
    await build({ entryPoints: [root + entry], outfile: root + output,
        bundle: true, platform: 'node', format: 'cjs', target: 'node22', external: ['vscode'] });
}
const suffix = process.platform === 'win32' ? '.exe' : '';
const target = new URL(`dist/inputmapping-lsp${suffix}`, import.meta.url);
// Replace the inode; overwriting a signed executable in place can cause a
// macOS SIGKILL at launch despite its bytes and signature being correct.
await rm(target, { force: true });
await copyFile(new URL(`../../target/release/inputmapping-lsp${suffix}`, import.meta.url), target);
if (!suffix) await chmod(target, 0o755);
