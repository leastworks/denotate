import assert from 'node:assert/strict';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { ensureEditorDependencies } from '../ensure-editor-deps.mjs';

async function fixture(t) {
    const directory = await mkdtemp(path.join(tmpdir(), 'den-deps-test-'));
    t.after(() => rm(directory, { recursive: true, force: true }));
    const manifest = { name: 'fixture', dependencies: { client: '1.0.0' }, devDependencies: { 'tree-sitter-cli': '0.25.10', esbuild: '0.25.12' } };
    await writeFile(path.join(directory, 'package.json'), JSON.stringify(manifest));
    await writeFile(path.join(directory, 'package-lock.json'), '{"lockfileVersion":3}');
    let installs = 0;
    const runInstall = async location => {
        assert.equal(location, directory);
        installs++;
        const modules = path.join(location, 'node_modules');
        await rm(modules, { recursive: true, force: true });
        const pkg = JSON.parse(await readFile(path.join(directory, 'package.json')));
        for (const file of [
            '.package-lock.json', ...Object.keys({ ...pkg.dependencies, ...pkg.devDependencies }).map(name => `${name}/package.json`),
            `tree-sitter-cli/tree-sitter${process.platform === 'win32' ? '.exe' : ''}`, 'esbuild/bin/esbuild'
        ]) {
            await mkdir(path.dirname(path.join(modules, file)), { recursive: true });
            await writeFile(path.join(modules, file), '{}');
        }
    };
    return { directory, manifest, options: { runInstall }, installs: () => installs };
}

test('first use installs once; unchanged dependencies are reused; force reinstalls', async t => {
    const f = await fixture(t);
    assert.equal(await ensureEditorDependencies(f.directory, f.options), true);
    assert.equal(await ensureEditorDependencies(f.directory, f.options), false);
    assert.equal(f.installs(), 1);
    assert.equal(await ensureEditorDependencies(f.directory, { ...f.options, force: true }), true);
    assert.equal(f.installs(), 2);
});

test('manifest and lockfile changes trigger installation', async t => {
    const f = await fixture(t);
    await ensureEditorDependencies(f.directory, f.options);
    f.manifest.dependencies.extra = '2.0.0';
    await writeFile(path.join(f.directory, 'package.json'), JSON.stringify(f.manifest));
    assert.equal(await ensureEditorDependencies(f.directory, f.options), true);
    await writeFile(path.join(f.directory, 'package-lock.json'), '{"lockfileVersion":3,"changed":true}');
    assert.equal(await ensureEditorDependencies(f.directory, f.options), true);
    assert.equal(await ensureEditorDependencies(f.directory, f.options), false);
    assert.equal(f.installs(), 3);
});

test('removed modules, direct packages and missing generator binaries are restored', async t => {
    const f = await fixture(t);
    await ensureEditorDependencies(f.directory, f.options);
    for (const missing of ['node_modules', 'node_modules/client',
        `node_modules/tree-sitter-cli/tree-sitter${process.platform === 'win32' ? '.exe' : ''}`]) {
        await rm(path.join(f.directory, missing), { recursive: true, force: true });
        assert.equal(await ensureEditorDependencies(f.directory, f.options), true);
    }
    assert.equal(f.installs(), 4);
});

test('changed installed lockfile or corrupt stamp cannot reuse stale dependencies', async t => {
    const f = await fixture(t);
    await ensureEditorDependencies(f.directory, f.options);
    await writeFile(path.join(f.directory, 'node_modules/.package-lock.json'), '{"changed":true}');
    assert.equal(await ensureEditorDependencies(f.directory, f.options), true);
    await writeFile(path.join(f.directory, 'node_modules/.denotate-install.json'), '{broken');
    assert.equal(await ensureEditorDependencies(f.directory, f.options), true);
    assert.equal(f.installs(), 3);
});

test('failed or incomplete installation is not stamped as successful', async t => {
    const f = await fixture(t);
    const stamp = path.join(f.directory, 'node_modules/.denotate-install.json');
    await assert.rejects(ensureEditorDependencies(f.directory, { runInstall: () => { throw new Error('offline'); } }), /offline/);
    await assert.rejects(readFile(stamp), { code: 'ENOENT' });
    await assert.rejects(ensureEditorDependencies(f.directory, { runInstall: () => {} }), /did not produce/);
    await assert.rejects(readFile(stamp), { code: 'ENOENT' });
    assert.equal(await ensureEditorDependencies(f.directory, f.options), true);
    assert.equal(await ensureEditorDependencies(f.directory, f.options), false);
});

test('each editor keeps its own dependency state', async t => {
    const a = await fixture(t), b = await fixture(t);
    await ensureEditorDependencies(a.directory, a.options);
    await ensureEditorDependencies(b.directory, b.options);
    await rm(path.join(a.directory, 'node_modules'), { recursive: true, force: true });
    assert.equal(await ensureEditorDependencies(b.directory, b.options), false);
    assert.equal(await ensureEditorDependencies(a.directory, a.options), true);
    assert.equal(a.installs(), 2);
    assert.equal(b.installs(), 1);
});
