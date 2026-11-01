import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { copyFile, mkdir, mkdtemp, readFile, rename, rm, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const editor = fileURLToPath(new URL('../', import.meta.url));
const script = fileURLToPath(import.meta.url);
// The grammar is self-contained. Add any future imported grammar helpers here.
const inputs = ['grammar.js', 'tree-sitter.json'];
const outputs = [
    'src/grammar.json', 'src/node-types.json', 'src/parser.c',
    'src/tree_sitter/alloc.h', 'src/tree_sitter/array.h', 'src/tree_sitter/parser.h'
];
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
async function readOptional(file) {
    try { return await readFile(file); }
    catch (error) { if (error.code === 'ENOENT') return null; throw error; }
}
async function outputHashes(directory) {
    const hashes = {};
    for (const file of outputs) {
        const bytes = await readOptional(path.join(directory, file));
        if (bytes === null) return null;
        hashes[file] = digest(bytes);
    }
    return hashes;
}

export async function generateParser({
    grammarDirectory = path.resolve(editor, '../../grammars/den'),
    cacheFile = path.resolve(editor, '../../target/den-parser-generation.json'),
    force = false
} = {}) {
    const executable = path.join(editor, 'node_modules/tree-sitter-cli',
        process.platform === 'win32' ? 'tree-sitter.exe' : 'tree-sitter');
    const installed = JSON.parse(await readFile(path.join(editor, 'node_modules/tree-sitter-cli/package.json')));
    const pinned = JSON.parse(await readFile(path.join(editor, 'package.json'))).devDependencies['tree-sitter-cli'];
    if (installed.version !== pinned) {
        throw new Error(`Expected tree-sitter-cli ${pinned}, found ${installed.version}; run npm ci --prefix editors/den.`);
    }
    const sources = await Promise.all(inputs.map(file => readFile(path.join(grammarDirectory, file))));
    const fingerprint = digest(JSON.stringify({
        inputs: sources.map(digest), generator: digest(await readFile(executable)),
        version: pinned, node: process.versions.node, script: digest(await readFile(script))
    }));
    let cached;
    try { cached = JSON.parse(await readOptional(cacheFile)); }
    catch (error) { if (!(error instanceof SyntaxError)) throw error; }
    const current = await outputHashes(grammarDirectory);
    if (!force && cached?.fingerprint === fingerprint && current !== null
        && JSON.stringify(cached.outputs) === JSON.stringify(current)) {
        return { generated: false, changed: [] };
    }

    // Generate away from Cargo's watched files. A grammar comment, missing stamp
    // or forced CI run must not touch parser timestamps when the bytes agree.
    await mkdir(path.dirname(cacheFile), { recursive: true });
    const temporary = await mkdtemp(path.join(path.dirname(cacheFile), 'den-parser-'));
    try {
        for (const [index, file] of inputs.entries()) {
            await writeFile(path.join(temporary, file), sources[index]);
        }
        const result = spawnSync(executable, ['generate'], { cwd: temporary, stdio: 'inherit' });
        if (result.error) throw result.error;
        if (result.status !== 0) throw new Error(`Parser generation failed (${result.signal ?? result.status}).`);
        const generated = await outputHashes(temporary);
        if (generated === null) throw new Error('Parser generation did not produce all expected files.');
        // Do not stamp a mixture if the grammar was edited while generation ran.
        for (const [index, file] of inputs.entries()) {
            if (!(await readFile(path.join(grammarDirectory, file))).equals(sources[index])) {
                throw new Error('Grammar changed during generation; retry the build.');
            }
        }
        const changed = [];
        for (const file of outputs) {
            const source = path.join(temporary, file);
            const destination = path.join(grammarDirectory, file);
            const existing = await readOptional(destination);
            if (existing === null || digest(existing) !== generated[file]) {
                await mkdir(path.dirname(destination), { recursive: true });
                await copyFile(source, destination);
                changed.push(file);
            }
        }
        const stamp = path.join(temporary, 'stamp.json');
        await writeFile(stamp, JSON.stringify({ fingerprint, outputs: generated }) + '\n');
        await rename(stamp, cacheFile);
        return { generated: true, changed };
    } finally {
        await rm(temporary, { recursive: true, force: true });
    }
}

if (process.argv[1] && path.resolve(process.argv[1]) === script) {
    const args = process.argv.slice(2);
    if (args.length > 1 || (args.length === 1 && args[0] !== '--force')) {
        throw new Error('Usage: generate-parser.mjs [--force]');
    }
    const result = await generateParser({ force: args.includes('--force') });
    console.log(result.generated
        ? `Denotate parser generated; ${result.changed.length} files changed.`
        : 'Denotate parser is current; generation skipped.');
}
