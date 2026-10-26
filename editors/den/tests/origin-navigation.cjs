const { test } = require('node:test');
const assert = require('node:assert/strict');
const { createHash } = require('node:crypto');
const { snapshotResolver, validate, goToOrigin } = require('../src/origin-navigation.cjs');
const hash = text => `sha256:${createHash('sha256').update(text).digest('hex')}`;
const uri = value => ({ scheme: value.split(':')[0], toString: () => value });
const descriptor = (text, extra = {}) => ({ uri: 'file:///lib/source.dsl', view: 'dsl', hash: hash(text), start: { line: 1, column: 1 }, end: { line: 1, column: 2 }, ...extra });
function harness(origins, text = 'abc') {
  const source = { uri: uri('file:///app/main.den'), languageId: 'denotate', version: 1 };
  const target = { getText: () => text, positionAt: offset => offset };
  const shown = [], warnings = [], choices = [];
  const vscode = {
    Uri: { parse: uri }, Range: class { constructor(start, end) { this.start = start; this.end = end; } },
    workspace: { openTextDocument: async () => target },
    window: {
      activeTextEditor: { document: source, selection: { active: { line: 0, character: 0 } } },
      showTextDocument: async (...args) => shown.push(args),
      showWarningMessage: text => warnings.push(text), showInformationMessage: text => warnings.push(text),
      showQuickPick: async items => { choices.push(items); return items.at(-1); }
    }
  };
  return { vscode, source, target, shown, warnings, choices, request: async () => ({ version: 1, origins }), resolve: async () => ({ text }) };
}
const run = h => goToOrigin(h.vscode, h.request, h.resolve);

test('exact scalar coordinates become UTF-16 offsets; LF only, BOM and CR retained', () => {
  const text = '\ufeffé😀\r\nZ\rQ';
  assert.deepEqual(validate(descriptor(text, { start: { line: 1, column: 3 }, end: { line: 2, column: 4 } }), { text }), { start: 2, end: 9 });
  for (const end of [{ line: 3, column: 1 }, { line: 1, column: 99 }, { line: 0, column: 1 }]) assert.throws(() => validate(descriptor(text, { end }), { text }), /outside/);
  assert.throws(() => validate(descriptor(text, { start: { line: 2, column: 1 } }), { text }), /reversed/);
  assert.throws(() => validate(descriptor(text), { text: text.slice(1) }), /hash/);
});

test('one matching dirty source opens exactly its verified range', async () => {
  const h = harness([descriptor('abc')]);
  h.resolve = async () => ({ text: 'abc', open: true, dirty: true });
  await run(h);
  assert.equal(h.choices.length, 0); assert.equal(h.shown.length, 1);
  assert.deepEqual({ ...h.shown[0][1].selection }, { start: 0, end: 1 });
});

test('picker retains library URIs, views, revisions and disjoint ranges, including unavailable choices', async () => {
  const h = harness([descriptor('old'), descriptor('abc', { view: 'other' }), descriptor('abc', { start: { line: 1, column: 3 }, end: { line: 1, column: 4 } })]);
  await run(h);
  assert.equal(h.choices[0].length, 3);
  assert.match(h.choices[0][0].detail, /Unavailable/);
  assert.equal(h.choices[0][1].label, 'file:///lib/source.dsl');
  assert.match(h.choices[0][1].description, /other/);
  assert.deepEqual({ ...h.shown[0][1].selection }, { start: 2, end: 3 });
});

test('cancelled picker never opens a source', async () => {
  const h = harness([descriptor('abc'), descriptor('abc', { view: 'other' })]);
  h.vscode.window.showQuickPick = async () => undefined;
  await run(h); assert.equal(h.shown.length, 0); assert.equal(h.warnings.length, 0);
});

test('changed, missing and unsupported sources are reported without navigation', async () => {
  for (const snapshot of [{ text: 'changed', open: true }, { unavailable: 'missing' }, { unavailable: 'No resolver' }]) {
    const h = harness([descriptor('abc')]); h.resolve = async () => snapshot;
    await run(h); assert.equal(h.shown.length, 0); assert.equal(h.warnings.length, 1);
  }
});

test('source changed while picker was open is revalidated', async () => {
  const h = harness([descriptor('abc'), descriptor('abc', { view: 'other' })]);
  let text = 'abc'; h.resolve = async () => ({ text });
  h.vscode.window.showQuickPick = async items => { text = 'changed'; return items[0]; };
  await run(h); assert.equal(h.shown.length, 0); assert.match(h.warnings[0], /hash/);
});

test('edits while opening a source or awaiting server response never use stale ranges', async () => {
  for (const change of ['target', 'den', 'response']) {
    const h = harness([descriptor('abc')]);
    if (change === 'response') h.request = async () => { ++h.source.version; return { version: 1, origins: [descriptor('abc')] }; };
    else h.vscode.workspace.openTextDocument = async () => {
      if (change === 'target') h.target.getText = () => 'changed'; else ++h.source.version;
      return h.target;
    };
    await run(h); assert.equal(h.shown.length, 0); assert.equal(h.warnings.length, 1);
  }
});

test('bridge uses all open buffers including canonical aliases; mismatching dirty buffer never reads disk', async () => {
  let reads = 0;
  const vscode = { Uri: { parse: uri }, workspace: {
    textDocuments: [{ uri: uri('file:///alias.dsl'), getText: () => 'dirty', isDirty: true, version: 7 }],
    fs: { readFile: async () => { ++reads; return Buffer.from('saved'); } }
  } };
  const resolve = snapshotResolver(vscode, () => 'same-file', new Map());
  const snapshot = await resolve({ uri: 'file:///source.dsl' });
  assert.equal(snapshot.text, 'dirty'); assert.equal(snapshot.version, 7);
  assert.throws(() => validate(descriptor('saved'), snapshot), /open buffer/);
  assert.equal(reads, 0);
});

test('bridge rejects racing disk replies, failed lookups and non-file sources; preserves exact bytes', async () => {
  for (const race of ['open', 'generation', 'failed', 'none']) {
    const generations = new Map(), documents = [];
    const vscode = { Uri: { parse: uri }, workspace: { textDocuments: documents, fs: { readFile: async () => {
      if (race === 'open') documents.push({ uri: uri('file:///source.dsl') });
      if (race === 'generation') generations.set('file:///source.dsl', 1);
      if (race === 'failed') throw new Error('denied');
      return Buffer.from('\ufeffa\r\n');
    } } } };
    const resolve = snapshotResolver(vscode, u => u.toString(), generations);
    const snapshot = await resolve({ uri: 'file:///source.dsl' });
    if (race === 'none') assert.equal(snapshot.text, '\ufeffa\r\n'); else assert.ok(snapshot.unavailable);
    assert.match((await resolve({ uri: 'https://example.org/source.dsl' })).unavailable, /No resolver/);
  }
});

test('conflicting canonical open aliases are unavailable, never chosen arbitrarily', async () => {
  const vscode = { Uri: { parse: uri }, workspace: { textDocuments: [
    { uri: uri('file:///first.dsl'), getText: () => 'saved' },
    { uri: uri('file:///alias.dsl'), getText: () => 'dirty' }
  ] } };
  const resolve = snapshotResolver(vscode, () => 'same-file', new Map());
  assert.match((await resolve({ uri: 'file:///first.dsl' })).unavailable, /disagree/);
});

test('malformed buffer text cannot hash as a replacement character', () => {
  assert.throws(() => validate(descriptor('\ufffd'), { text: '\ud800' }), /surrogate/);
});

test('UTF-8 signature metadata reconstructs exact bytes and projects visible offsets', async () => {
  const { documentSnapshot } = require('../src/origin-navigation.cjs');
  const text = '\ufeffA😀x\r\nZ';
  const origin = descriptor(text, { start: { line: 1, column: 3 }, end: { line: 2, column: 2 } });
  const doc = { encoding: 'utf8bom', getText: () => text.slice(1) };
  assert.deepEqual(validate(origin, documentSnapshot(doc)), { start: 1, end: 7 });
  doc.getText = () => 'changed';
  assert.throws(() => validate(origin, documentSnapshot(doc)), /hash/);
  // A second FEFF is actual buffer content; do not strip or deduplicate it.
  doc.getText = () => '\ufeffA';
  assert.equal(documentSnapshot(doc).text, '\ufeff\ufeffA');
  const double = descriptor('\ufeff\ufeffA', { start: { line: 1, column: 3 }, end: { line: 1, column: 4 } });
  assert.deepEqual(validate(double, documentSnapshot(doc)), { start: 1, end: 2 });
  doc.encoding = 'utf8';
  assert.equal(documentSnapshot(doc).bom, false);
  assert.equal(documentSnapshot(doc).text, '\ufeffA');
  assert.throws(() => validate(double, documentSnapshot(doc)), /hash/);
});

test('BOM buffer authority needs no disk read and encoding-only changes invalidate identity', async () => {
  const doc = { uri: uri('file:///source.dsl'), encoding: 'utf8bom', getText: () => 'abc', version: 1 };
  const vscode = { Uri: { parse: uri }, workspace: { textDocuments: [doc] } };
  const resolve = snapshotResolver(vscode, u => u.toString(), new Map());
  const origin = descriptor('\ufeffabc', { start: { line: 1, column: 2 }, end: { line: 1, column: 5 } });
  assert.deepEqual(validate(origin, await resolve({ uri: doc.uri.toString() })), { start: 0, end: 3 });
  doc.encoding = 'utf8';
  assert.throws(() => validate(origin, { text: 'abc' }), /hash/);
  assert.equal((await resolve({ uri: doc.uri.toString() })).text, 'abc');
});
