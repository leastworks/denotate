import assert from 'node:assert/strict';
import { readFile, access, constants } from 'node:fs/promises';
import test from 'node:test';

const root = new URL('../', import.meta.url);
const read = file => readFile(new URL(file, root), 'utf8');

test('the editor example is the existing lowering/provenance fixture', async () => {
    assert.equal(await read('examples/overlap.testdsl'), await read('../../crates/test-dsl/fixtures/overlapping-mappings.txt'));
});

test('language registration and built entry points exist', async () => {
    const manifest = JSON.parse(await read('package.json'));
    const language = manifest.contributes.languages[0];
    assert.equal(language.id, 'testdsl');
    assert.deepEqual(language.extensions, ['.testdsl']);
    const grammar = manifest.contributes.grammars[0];
    assert.equal(grammar.language, language.id);
    assert.equal(JSON.parse(await read(grammar.path)).scopeName, grammar.scopeName);
    assert.equal(JSON.parse(await read(language.configuration)).comments.lineComment, '//');
    for (const entry of [manifest.main, 'dist/vscode-smoke.cjs']) {
        assert.ok((await read(entry)).length > 0);
    }
    const suffix = process.platform === 'win32' ? '.exe' : '';
    await access(new URL(`dist/test-dsl-lsp${suffix}`, root), constants.X_OK);
    assert.deepEqual(await readFile(new URL(`dist/test-dsl-lsp${suffix}`, root)),
        await readFile(new URL(`../../target/release/test-dsl-lsp${suffix}`, root)));
});

test('F5 builds this extension and opens only its example directory', async () => {
    const launch = JSON.parse(await read('.vscode/launch.json')).configurations[0];
    assert.equal(launch.type, 'extensionHost');
    assert.deepEqual(launch.args, ['--extensionDevelopmentPath=${workspaceFolder}', '${workspaceFolder}/examples']);
    const task = JSON.parse(await read('.vscode/tasks.json')).tasks[0];
    assert.equal(launch.preLaunchTask, task.label);
    assert.equal(task.type, 'npm');
    assert.equal(task.script, 'build');
});
