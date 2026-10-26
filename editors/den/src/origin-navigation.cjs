const { createHash } = require('node:crypto');

// VS Code keeps the UTF-8 signature in encoding metadata, outside getText().
// Reconstruct exact source text for hashing; retain the hidden prefix separately
// so origin coordinates can be projected into the visible editor buffer.
function documentSnapshot(document) {
  const bom = document.encoding === 'utf8bom';
  return { text: (bom ? '\ufeff' : '') + document.getText(), bom, open: true };
}

// Shared by the server bridge and navigation. An open buffer in any language
// is authoritative, including a dirty buffer that disagrees with saved bytes.
function snapshotResolver(vscode, canonical, generations) {
  return async ({ uri }) => {
    const target = vscode.Uri.parse(uri), key = canonical(target);
    const start = generations.get(key) ?? 0;
    const open = () => vscode.workspace.textDocuments.filter(d => canonical(d.uri) === key);
    const documents = open(), document = documents[0];
    if (document) {
      const snapshot = documentSnapshot(document);
      if (documents.some(d => { const other = documentSnapshot(d); return other.text !== snapshot.text || other.bom !== snapshot.bom; })) return { uri, unavailable: 'Open buffers for this source disagree' };
      return { uri, bufferUri: document.uri.toString(), ...snapshot, dirty: document.isDirty, version: document.version, generation: start };
    }
    if (target.scheme !== 'file') return { uri, unavailable: 'No resolver for this source URI' };
    try {
      const bytes = await vscode.workspace.fs.readFile(target);
      if (start !== (generations.get(key) ?? 0) || open().length) return { uri, unavailable: 'Snapshot changed during lookup' };
      const text = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(bytes);
      return { uri, text, bom: text.startsWith('\ufeff'), open: false, dirty: false, generation: start };
    } catch (error) { return { uri, unavailable: String(error) }; }
  };
}

// Stored columns count scalars and only LF ends a line. The returned offsets
// count UTF-16 units in the exact source text. validate then removes only the
// signature hidden by the editor before passing offsets to positionAt.
function offset(text, target) {
  let line = 1, column = 1, at = 0;
  for (const scalar of text) {
    if (line === target.line && column === target.column) return at;
    at += scalar.length;
    if (scalar === '\n') { ++line; column = 1; } else ++column;
  }
  if (line === target.line && column === target.column) return at;
  throw new Error('Origin range is outside the source snapshot');
}
function validate(origin, snapshot) {
  if (typeof snapshot.text !== 'string') throw new Error(snapshot.unavailable ?? 'Source snapshot unavailable');
  if (!snapshot.text.isWellFormed()) throw new Error('Source contains an unpaired UTF-16 surrogate');
  const hash = `sha256:${createHash('sha256').update(snapshot.text, 'utf8').digest('hex')}`;
  if (hash !== origin.hash) throw new Error(`Source changed${snapshot.open ? ' in the open buffer' : ''}; its hash does not match the recorded origin`);
  const start = offset(snapshot.text, origin.start), end = offset(snapshot.text, origin.end);
  if (end < start) throw new Error('Origin range is reversed');
  const hidden = snapshot.bom ? 1 : 0;
  return { start: Math.max(0, start - hidden), end: Math.max(0, end - hidden) };
}

async function goToOrigin(vscode, request, resolve) {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'denotate') return;
  const source = editor.document, version = source.version;
  const current = () => {
    if (source.isClosed || source.version !== version) throw new Error('The .den document changed; request origins again');
  };
  try {
    const result = await request('denotate/origins', { textDocument: { uri: source.uri.toString(), version }, position: editor.selection.active });
    current();
    if (result.version !== version) throw new Error('The .den document is out of sync; request origins again');
    if (!result.origins.length) { void vscode.window.showInformationMessage('No embedded origin at this occurrence.'); return; }
    const choices = await Promise.all(result.origins.map(async origin => {
      let unavailable;
      try { validate(origin, await resolve({ uri: origin.uri })); } catch (error) { unavailable = error.message; }
      return {
        label: origin.uri,
        description: `${origin.view} · ${origin.start.line}:${origin.start.column}–${origin.end.line}:${origin.end.column}`,
        detail: `${origin.hash}${unavailable ? ` · Unavailable: ${unavailable}` : ''}`,
        origin
      };
    }));
    current();
    const chosen = choices.length === 1 ? choices[0] : await vscode.window.showQuickPick(choices, { title: 'Denotate: Go to Origin', placeHolder: 'Choose a source, view and range' });
    if (!chosen) return;
    current();
    // A picker may stay open while either source changes. Resolve afresh, then
    // check the actual opened document again before displaying any location.
    const snapshot = await resolve({ uri: chosen.origin.uri });
    validate(chosen.origin, snapshot);
    current();
    const document = await vscode.workspace.openTextDocument(vscode.Uri.parse(snapshot.bufferUri ?? chosen.origin.uri));
    const range = validate(chosen.origin, documentSnapshot(document));
    current();
    await vscode.window.showTextDocument(document, { selection: new vscode.Range(document.positionAt(range.start), document.positionAt(range.end)), preview: true });
  } catch (error) { void vscode.window.showWarningMessage(`Cannot go to origin: ${error.message}`); }
}

module.exports = { snapshotResolver, documentSnapshot, validate, goToOrigin };
