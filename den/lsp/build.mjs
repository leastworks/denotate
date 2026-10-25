import { build } from 'esbuild';
import { copyFile, mkdir, chmod, rm } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
const root = fileURLToPath(new URL('.', import.meta.url));
await mkdir(new URL('dist/', import.meta.url), { recursive: true });
await build({ entryPoints: [`${root}src/extension.cjs`], outfile: `${root}dist/extension.cjs`,
    bundle: true, platform: 'node', format: 'cjs', target: 'node22', external: ['vscode'] });
await build({ entryPoints: [`${root}tests/vscode-smoke.cjs`], outfile: `${root}dist/vscode-smoke.cjs`,
    bundle: true, platform: 'node', format: 'cjs', target: 'node22', external: ['vscode'] });
for (const [from, to] of [
    ['language-configuration.json', 'dist/language-configuration.json'],
    ['syntaxes/denotate.tmLanguage.json', 'dist/denotate.tmLanguage.json']
]) await copyFile(new URL(from, import.meta.url), new URL(to, import.meta.url));
const suffix = process.platform === 'win32' ? '.exe' : '';
const target = new URL(`dist/denotate-lsp${suffix}`, import.meta.url);
// Replace the inode: overwriting a signed executable can leave stale macOS
// code-signing state and cause SIGKILL at launch, even with identical bytes.
await rm(target, { force: true });
await copyFile(new URL(`../../target/release/denotate-lsp${suffix}`, import.meta.url), target);
if (!suffix) await chmod(target, 0o755);
