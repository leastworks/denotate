import assert from 'node:assert/strict';
import { mkdtemp, readFile, rm, stat, utimes, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { generateParser } from '../scripts/generate-parser.mjs';

async function fixture(t) {
    const directory = await mkdtemp(path.join(tmpdir(), 'den-parser-test-'));
    t.after(() => rm(directory, { recursive: true, force: true }));
    const grammar = "module.exports = grammar({name: 'denotate', rules: {source_file: $ => repeat('hello')}});\n";
    const configuration = await readFile(new URL('../../../grammars/den/tree-sitter.json', import.meta.url));
    await writeFile(path.join(directory, 'grammar.js'), grammar);
    await writeFile(path.join(directory, 'tree-sitter.json'), configuration);
    return {
        directory, grammar, configuration,
        options: { grammarDirectory: directory, cacheFile: path.join(directory, 'cache/generation.json') },
        parser: path.join(directory, 'src/parser.c')
    };
}

// Actual pinned generator, isolated grammars: these checks cover the build behavior,
// including timestamps, which determine whether Cargo recompiles the C parser.
test('unchanged, comment-only and forced generation preserve generated files', async t => {
    const f = await fixture(t);
    assert.equal((await generateParser(f.options)).generated, true);
    const stamp = JSON.parse(await readFile(f.options.cacheFile));
    const date = new Date('2001-01-01T00:00:00Z');
    for (const file of Object.keys(stamp.outputs)) await utimes(path.join(f.directory, file), date, date);
    assert.deepEqual(await generateParser(f.options), { generated: false, changed: [] });
    await writeFile(path.join(f.directory, 'grammar.js'), f.grammar + '// Authoring comment.\n');
    assert.deepEqual(await generateParser(f.options), { generated: true, changed: [] });
    assert.deepEqual(await generateParser({ ...f.options, force: true }), { generated: true, changed: [] });
    for (const file of Object.keys(stamp.outputs)) {
        assert.equal((await stat(path.join(f.directory, file))).mtimeMs, date.getTime(), file);
    }
});

test('grammar and configuration changes invalidate the cache', async t => {
    const f = await fixture(t);
    await generateParser(f.options);
    const before = await readFile(f.parser);
    await writeFile(path.join(f.directory, 'grammar.js'), f.grammar.replace('hello', 'goodbye'));
    assert.ok((await generateParser(f.options)).changed.includes('src/parser.c'));
    assert.notDeepEqual(await readFile(f.parser), before);
    const configuration = JSON.parse(f.configuration);
    configuration.metadata.description = 'Changed metadata';
    await writeFile(path.join(f.directory, 'tree-sitter.json'), JSON.stringify(configuration));
    assert.equal((await generateParser(f.options)).generated, true);
    assert.equal((await generateParser(f.options)).generated, false);
});

test('missing or modified outputs are repaired even with a matching input stamp', async t => {
    const f = await fixture(t);
    await generateParser(f.options);
    const original = await readFile(f.parser);
    await writeFile(f.parser, 'damaged parser');
    assert.ok((await generateParser(f.options)).changed.includes('src/parser.c'));
    assert.deepEqual(await readFile(f.parser), original);
    const header = 'src/tree_sitter/parser.h';
    await rm(path.join(f.directory, header));
    assert.ok((await generateParser(f.options)).changed.includes(header));
    assert.equal((await generateParser(f.options)).generated, false);
});

test('missing, corrupt or outdated stamps regenerate without rewriting identical outputs', async t => {
    const f = await fixture(t);
    await generateParser(f.options);
    await rm(f.options.cacheFile);
    assert.deepEqual(await generateParser(f.options), { generated: true, changed: [] });
    await writeFile(f.options.cacheFile, '{broken');
    assert.deepEqual(await generateParser(f.options), { generated: true, changed: [] });
    const stamp = JSON.parse(await readFile(f.options.cacheFile));
    stamp.fingerprint = 'older toolchain or generation wrapper';
    await writeFile(f.options.cacheFile, JSON.stringify(stamp));
    assert.deepEqual(await generateParser(f.options), { generated: true, changed: [] });
});

test('failed generation preserves the previous outputs and stamp', async t => {
    const f = await fixture(t);
    await generateParser(f.options);
    const before = await readFile(f.parser);
    const stamp = await readFile(f.options.cacheFile);
    await writeFile(path.join(f.directory, 'grammar.js'), 'not valid JavaScript!');
    await assert.rejects(generateParser(f.options), /Parser generation failed/);
    assert.deepEqual(await readFile(f.parser), before);
    assert.deepEqual(await readFile(f.options.cacheFile), stamp);
    await writeFile(path.join(f.directory, 'grammar.js'), f.grammar);
    assert.equal((await generateParser(f.options)).generated, false);
});
