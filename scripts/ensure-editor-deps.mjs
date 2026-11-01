import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('../', import.meta.url));
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
async function optional(file) {
    try { return await readFile(file); }
    catch (error) { if (error.code === 'ENOENT') return null; throw error; }
}
function install(directory) {
    const result = spawnSync('npm', ['ci', '--prefix', directory, '--no-audit', '--no-fund'], {
        stdio: 'inherit'
    });
    if (result.error) throw result.error;
    if (result.status !== 0) throw new Error(`Dependency installation failed (${result.signal ?? result.status}).`);
}

export async function ensureEditorDependencies(directory, { force = false, runInstall = install } = {}) {
    if (Number(process.versions.node.split('.')[0]) < 22) {
        throw new Error('Denotate requires Node 22 or newer.');
    }
    const manifest = await readFile(path.join(directory, 'package.json'));
    const lock = await readFile(path.join(directory, 'package-lock.json'));
    const packageJson = JSON.parse(manifest);
    const fingerprint = hash(JSON.stringify({
        schema: 1, manifest: hash(manifest), lock: hash(lock),
        node: process.versions.node, platform: process.platform, arch: process.arch
    }));
    const modules = path.join(directory, 'node_modules');
    const stampPath = path.join(modules, '.denotate-install.json');
    const required = [
        ...Object.keys({ ...packageJson.dependencies, ...packageJson.devDependencies })
            .map(name => `${name}/package.json`)
    ];
    if (packageJson.devDependencies?.['tree-sitter-cli']) {
        required.push(`tree-sitter-cli/tree-sitter${process.platform === 'win32' ? '.exe' : ''}`);
    }
    if (packageJson.devDependencies?.esbuild) required.push('esbuild/bin/esbuild');
    async function installedState() {
        const hiddenLock = await optional(path.join(modules, '.package-lock.json'));
        if (!hiddenLock) return null;
        for (const file of required) {
            try { if (!(await stat(path.join(modules, file))).isFile()) return null; }
            catch (error) { if (error.code === 'ENOENT') return null; throw error; }
        }
        return hash(hiddenLock);
    }
    let stamp;
    try { stamp = JSON.parse(await optional(stampPath)); }
    catch (error) { if (!(error instanceof SyntaxError)) throw error; }
    const state = await installedState();
    if (!force && state !== null && stamp?.fingerprint === fingerprint && stamp.installed === state) {
        return false;
    }
    console.log(`Installing pinned dependencies for ${packageJson.name}…`);
    await runInstall(directory);
    const installed = await installedState();
    if (installed === null) throw new Error('Dependency installation did not produce the required packages and tools.');
    await writeFile(stampPath, JSON.stringify({ fingerprint, installed }) + '\n');
    return true;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
    const [editor, ...args] = process.argv.slice(2);
    if (!['den', 'test-dsl'].includes(editor) || args.length > 1 || (args.length && args[0] !== '--force')) {
        throw new Error('Usage: ensure-editor-deps.mjs den|test-dsl [--force]');
    }
    await ensureEditorDependencies(path.join(root, 'editors', editor), { force: args.includes('--force') });
}
