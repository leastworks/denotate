import assert from 'node:assert/strict';
import { readFile, access, constants } from 'node:fs/promises';
import test from 'node:test';
import { createHash } from 'node:crypto';

const root = new URL('../', import.meta.url);
const read = file => readFile(new URL(file, root), 'utf8');

test('pre-mask snapshot and embedded fixture sources retain their recorded hashes', async () => {
    const bytes = await read('../fixtures/pre-mask.json');
    const data = JSON.parse(bytes);
    const hashes = JSON.parse(await read('../fixtures/pre-mask-sources.json'));
    const hash = text => createHash('sha256').update(text).digest('hex');
    assert.equal(data.revision, hashes.revision);
    assert.equal(hash(bytes), hashes.artifact_sha256);
    assert.deepEqual(data.cases.map(c => hash(c.text)), hashes.source_sha256);
});

test('the editor example is the existing lowering/provenance fixture', async () => {
    assert.equal(await read('examples/overlap.inputmapping'), await read('../fixtures/overlapping-mappings.txt'));
});

test('language registration and built entry points exist', async () => {
    const manifest = JSON.parse(await read('package.json'));
    const language = manifest.contributes.languages[0];
    assert.equal(language.id, 'inputmapping');
    assert.deepEqual(language.extensions, ['.inputmapping']);
    const grammar = manifest.contributes.grammars[0];
    assert.equal(grammar.language, language.id);
    assert.equal(JSON.parse(await read(grammar.path)).scopeName, grammar.scopeName);
    assert.equal(JSON.parse(await read(language.configuration)).comments.lineComment, '//');
    for (const entry of [manifest.main, 'dist/vscode-smoke.cjs']) {
        assert.ok((await read(entry)).length > 0);
    }
    const suffix = process.platform === 'win32' ? '.exe' : '';
    await access(new URL(`dist/inputmapping-lsp${suffix}`, root), constants.X_OK);
    assert.deepEqual(await readFile(new URL(`dist/inputmapping-lsp${suffix}`, root)),
        await readFile(new URL(`../../target/release/inputmapping-lsp${suffix}`, root)));
});

test('F5 builds this extension and opens only its example directory', async () => {
    const launch = JSON.parse(await read('.vscode/launch.json')).configurations[0];
    assert.equal(launch.type, 'extensionHost');
    assert.deepEqual(launch.args, ['--extensionDevelopmentPath=${workspaceFolder}', '${workspaceFolder}/examples']);
    const task = JSON.parse(await read('.vscode/tasks.json')).tasks[0];
    assert.equal(launch.preLaunchTask, task.label);
    assert.equal(task.script, 'build');
});
