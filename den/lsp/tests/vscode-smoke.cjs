const assert = require('node:assert/strict');
const vscode = require('vscode');

exports.run = async function () {
    const extension = vscode.extensions.getExtension('denotate.denotate');
    assert.ok(extension);
    await extension.activate();
    const folder = vscode.workspace.workspaceFolders[0].uri;
    const uri = vscode.Uri.joinPath(folder, 'computation.den');
    const document = await vscode.workspace.openTextDocument(uri);
    await vscode.window.showTextDocument(document);
    assert.equal(document.languageId, 'denotate');
    assert.equal(extension.packageJSON.contributes.grammars[0].scopeName, 'source.denotate');
    const symbols = await vscode.commands.executeCommand('vscode.executeDocumentSymbolProvider', uri);
    assert.ok(symbols.some(symbol => symbol.name === 'sort Slot'));
    assert.ok(symbols.some(symbol => symbol.name === 'available(D) :- …'));

    async function editAndWait(edit, broken) {
        // Register before the edit: no polling or sleeps, and keep an upper bound.
        const done = new Promise((resolve, reject) => {
            const timer = setTimeout(() => { subscription.dispose(); reject(new Error('Diagnostics timed out')); }, 10000);
            const subscription = vscode.languages.onDidChangeDiagnostics(event => {
                if (!event.uris.some(value => value.toString() === uri.toString())) return;
                const errors = vscode.languages.getDiagnostics(uri).filter(d => d.severity === vscode.DiagnosticSeverity.Error);
                if ((errors.length > 0) === broken) {
                    clearTimeout(timer); subscription.dispose(); resolve();
                }
            });
        });
        assert.ok(await vscode.workspace.applyEdit(edit));
        await done;
    }
    const offset = document.getText().indexOf('sort Slot;') + 'sort Slot'.length;
    const at = document.positionAt(offset);
    const remove = new vscode.WorkspaceEdit();
    remove.delete(uri, new vscode.Range(at, document.positionAt(offset + 1)));
    await editAndWait(remove, true);
    const repair = new vscode.WorkspaceEdit();
    repair.insert(uri, at, ';');
    await editAndWait(repair, false);
    const exampleUri = vscode.Uri.joinPath(folder, 'example.den');
    const example = await vscode.workspace.openTextDocument(exampleUri);
    await vscode.window.showTextDocument(example);
    const call = example.getText().indexOf('mapped_to(input_a, a)');
    assert.ok(call >= 0);
    const definitions = await vscode.commands.executeCommand('vscode.executeDefinitionProvider', exampleUri, example.positionAt(call));
    assert.equal(definitions.length, 1);
    assert.equal((definitions[0].targetUri ?? definitions[0].uri).toString(), uri.toString());
    const constants = await vscode.commands.executeCommand('vscode.executeCompletionItemProvider', exampleUri, example.positionAt(call + 18));
    assert.ok(constants.items.some(item => item.label === 'a'));
    assert.ok(!constants.items.some(item => item.label === 'input_a'));
    const references = await vscode.commands.executeCommand('vscode.executeReferenceProvider', exampleUri, example.positionAt(call));
    assert.ok(references.some(reference => reference.uri.toString() === uri.toString()));
    assert.ok(references.some(reference => reference.uri.toString() === exampleUri.toString()));
    const hovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', exampleUri, example.positionAt(call));
    // Match the client's actual plaintext-to-Markdown conversion, as A does.
    const expectedHover = new vscode.MarkdownString().appendText('relation mapped_to(source: Source, slot: Slot)').value;
    const hoverTexts = hovers.flatMap(hover => hover.contents.map(content => typeof content === 'string' ? content : content.value));
    assert.ok(hoverTexts.includes(expectedHover), JSON.stringify(hoverTexts));
    const signature = await vscode.commands.executeCommand('vscode.executeSignatureHelpProvider', exampleUri, example.positionAt(call + 18));
    assert.equal(signature.activeParameter, 1);
    assert.ok(signature.signatures[0].label.includes('slot: Slot'));

    const originalExample = example.getText();
    const originalLibrary = document.getText();
    const rename = await vscode.commands.executeCommand('vscode.executeDocumentRenameProvider', exampleUri, example.positionAt(call), 'mapping');
    assert.ok(await vscode.workspace.applyEdit(rename));
    assert.equal(example.getText(), originalExample.replaceAll('mapped_to', 'mapping'));
    assert.equal(document.getText(), originalLibrary.replaceAll('mapped_to', 'mapping'));
    const undo = await vscode.commands.executeCommand('vscode.executeDocumentRenameProvider', exampleUri, example.positionAt(call), 'mapped_to');
    assert.ok(await vscode.workspace.applyEdit(undo));
    assert.equal(example.getText(), originalExample);
    assert.equal(document.getText(), originalLibrary);

    const options = { tabSize: 4, insertSpaces: true };
    const edits = await vscode.commands.executeCommand('vscode.executeFormatDocumentProvider', uri, options);
    assert.ok(edits.length > 0, 'formatting must do useful work');
    const formatting = new vscode.WorkspaceEdit();
    formatting.set(uri, edits);
    assert.ok(await vscode.workspace.applyEdit(formatting));
    assert.ok(document.getText().includes('given(D) :-\n    supplies(_, D);'));
    // VS Code can normalize a provider's empty edit list to undefined.
    const secondFormat = await vscode.commands.executeCommand('vscode.executeFormatDocumentProvider', uri, options);
    assert.equal(secondFormat?.length ?? 0, 0);
    const api = extension.exports;
    async function eventually(probe, accept, label) {
        const until = Date.now() + 10000;
        while (Date.now() < until) {
            const value = await probe(); if (accept(value)) return value;
            await new Promise(resolve => setTimeout(resolve, 30));
        }
        throw new Error(`Timed out: ${label}`);
    }
    const rootUri = vscode.Uri.joinPath(folder, 'den.root');
    const rootDoc = await vscode.workspace.openTextDocument(rootUri);
    const rootText = rootDoc.getText();
    const replace = async (doc, text) => {
        const edit = new vscode.WorkspaceEdit();
        edit.replace(doc.uri, new vscode.Range(doc.positionAt(0), doc.positionAt(doc.getText().length)), text);
        assert.ok(await vscode.workspace.applyEdit(edit));
    };
    await replace(rootDoc, '{unfinished');
    await eventually(() => api.request('denotate/roots', { uri: exampleUri.toString() }), r => r.state === 'invalid', 'dirty manifest blocks root');
    await replace(rootDoc, rootText);
    await eventually(() => api.request('denotate/roots', { uri: exampleUri.toString() }), r => r.state === 'ready', 'manifest repair restores root');

    const originUri = vscode.Uri.joinPath(folder, 'origin.inputmapping');
    await vscode.workspace.fs.writeFile(originUri, Buffer.from('saved source'));
    const origin = await vscode.workspace.openTextDocument(originUri);
    const hash = 'sha256:' + require('node:crypto').createHash('sha256').update('saved source').digest('hex');
    const denUri = vscode.Uri.joinPath(folder, 'origin-test.den');
    await vscode.workspace.fs.writeFile(denUri, Buffer.from(`relation origin_test(); #s=source(${JSON.stringify(originUri.toString())},view:"dsl",hash:"${hash}"); origin_test() loc(#s 1:1 to 1:6);`));
    await vscode.workspace.openTextDocument(denUri);
    await eventually(() => api.request('denotate/originStatus', { uri: originUri.toString() }), r => r.state === 'matching', 'open DSL source matches');
    await replace(origin, 'dirty source');
    const dirty = await eventually(() => api.request('denotate/originStatus', { uri: originUri.toString() }), r => r.state === 'hash-mismatch', 'dirty DSL source wins over disk');
    assert.equal(dirty.snapshot.open, true); assert.equal(dirty.snapshot.dirty, true);
    await replace(origin, 'saved source');
    await eventually(() => api.request('denotate/originStatus', { uri: originUri.toString() }), r => r.state === 'matching', 'matching dirty buffer is accepted');

    // Actual checked findings must keep semantics and drop stale upstream links
    // while a dirty DSL buffer differs from the exported content identity.
    const checkedFolder = vscode.Uri.joinPath(folder, 'checked');
    await vscode.workspace.fs.createDirectory(checkedFolder);
    await vscode.workspace.fs.writeFile(vscode.Uri.joinPath(checkedFolder, 'den.root'), Buffer.from('{}'));
    const checkedUri = vscode.Uri.joinPath(checkedFolder, 'program.den');
    const checkedText = `sort S; const a,b:S; relation p(x:S);
#s=source(${JSON.stringify(originUri.toString())},view:"dsl",hash:"${hash}");
p(a) loc(#s 1:1 to 1:6); p(b) loc(#s 1:7 to 1:13);
obligation unique: at_most_one(p, group_by: ());`;
    await vscode.workspace.fs.writeFile(checkedUri, Buffer.from(checkedText));
    const checkedDoc = await vscode.workspace.openTextDocument(checkedUri);
    await vscode.window.showTextDocument(checkedDoc);
    const conflicts = () => vscode.languages.getDiagnostics(checkedUri).filter(d => d.code === 'counterexample');
    const links = ds => ds.flatMap(d => d.relatedInformation ?? []).filter(r => r.location.uri.toString() === originUri.toString());
    await eventually(conflicts, ds => ds.length === 2 && links(ds).length >= 2, 'published conflict links to matching dirty DSL buffer');
    await replace(origin, 'dirty source');
    await eventually(async () => ({ status: await api.request('denotate/roots', { uri: checkedUri.toString() }), diagnostics: conflicts() }), r => r.status.checking === 'complete' && r.status.originNotices?.length === 1 && r.diagnostics.length === 2 && links(r.diagnostics).length === 0, 'dirty origin removes links and retains findings');
    await replace(origin, 'saved source');
    await eventually(conflicts, ds => ds.length === 2 && links(ds).length >= 2, 'matching dirty source restores checked links');
    await replace(checkedDoc, checkedText.replace('p(b) loc(#s 1:7 to 1:13);', ''));
    await eventually(async () => ({ status: await api.request('denotate/roots', { uri: checkedUri.toString() }), diagnostics: conflicts() }), r => r.status.checking === 'complete' && r.status.summary?.state === 'proved' && r.diagnostics.length === 0, 'dirty den member repairs conflict before save');
    await replace(checkedDoc, checkedText);
    await eventually(conflicts, ds => ds.length === 2, 'dirty den member restores conflict');

    // The installed command follows a matching dirty non-.den buffer and
    // refuses a changed one even while its saved bytes still match the origin.
    const navigate = async () => {
        const editor = await vscode.window.showTextDocument(checkedDoc);
        const at = checkedDoc.positionAt(checkedDoc.getText().indexOf('p(b)'));
        editor.selection = new vscode.Selection(at, at);
        await vscode.commands.executeCommand('denotate.goToOrigin');
    };
    await navigate();
    assert.equal(vscode.window.activeTextEditor.document.uri.toString(), originUri.toString());
    assert.equal(vscode.window.activeTextEditor.document.getText(vscode.window.activeTextEditor.selection), 'source');
    await replace(origin, 'dirty source');
    await navigate();
    assert.equal(vscode.window.activeTextEditor.document.uri.toString(), checkedUri.toString(), 'changed open origin must never navigate to matching disk');
    await replace(origin, 'saved source');

    // Scalar columns are interpreted against the exact CRLF/astral snapshot,
    // then converted to the target editor's UTF-16 positions.
    const unicodeUri = vscode.Uri.joinPath(checkedFolder, 'unicode.dsl');
    const unicodeText = 'é😀x\r\nZ';
    await vscode.workspace.fs.writeFile(unicodeUri, Buffer.from(unicodeText));
    const unicodeHash = 'sha256:' + require('node:crypto').createHash('sha256').update(unicodeText).digest('hex');
    const unicodeDen = `relation unicode_origin(); unicode_origin() loc(#u 1:2 to 2:2); #u = source(${JSON.stringify(unicodeUri.toString())}, view: "dsl", hash: "${unicodeHash}");`;
    await replace(checkedDoc, unicodeDen);
    const unicodeEditor = await vscode.window.showTextDocument(checkedDoc);
    const unicodeAt = checkedDoc.positionAt(unicodeDen.indexOf('unicode_origin() loc'));
    unicodeEditor.selection = new vscode.Selection(unicodeAt, unicodeAt);
    await vscode.commands.executeCommand('denotate.goToOrigin');
    assert.equal(vscode.window.activeTextEditor.document.uri.toString(), unicodeUri.toString());
    assert.equal(vscode.window.activeTextEditor.document.getText(vscode.window.activeTextEditor.selection), '😀x\r\nZ');
    await replace(checkedDoc, checkedText);

    // Real VS Code decoding removes the UTF-8 signature from getText().
    const bomUri = vscode.Uri.joinPath(checkedFolder, 'bom.inputmapping');
    const bomText = '\ufeffA😀x\r\nZ';
    await vscode.workspace.fs.writeFile(bomUri, Buffer.from(bomText));
    const bomHash = 'sha256:' + require('node:crypto').createHash('sha256').update(bomText).digest('hex');
    const bomDen = checkedText.replace(originUri.toString(), bomUri.toString()).replace(hash, bomHash)
        .replace('1:1 to 1:6', '1:2 to 1:3').replace('1:7 to 1:13', '1:3 to 1:5');
    await replace(checkedDoc, bomDen);
    await eventually(() => api.request('denotate/originStatus', { uri: bomUri.toString() }), r => r.state === 'matching' && r.snapshot.open === false, 'closed BOM source matches exact disk bytes');
    await navigate();
    assert.equal(vscode.window.activeTextEditor.document.uri.toString(), bomUri.toString(), 'closed BOM source opens at its origin');
    const bomDoc = vscode.window.activeTextEditor.document;
    assert.equal(bomDoc.encoding, 'utf8bom');
    assert.equal(bomDoc.getText(), 'A😀x\r\nZ');
    console.log('BOM reproduction: encoding=' + bomDoc.encoding + ', getText=' + JSON.stringify(bomDoc.getText()));
    await eventually(() => api.request('denotate/originStatus', { uri: bomUri.toString() }), r => r.state === 'matching' && r.snapshot.open, 'open BOM source retains exact signature identity');
    const bomLinks = ds => ds.flatMap(d => d.relatedInformation ?? []).filter(r => r.location.uri.toString() === bomUri.toString());
    const bomFindings = await eventually(conflicts, ds => ds.length === 2 && bomLinks(ds).length >= 2, 'BOM source retains both related links');
    assert.deepEqual([...new Set(bomLinks(bomFindings).map(r => bomDoc.getText(r.location.range)))].sort(), ['A', '😀x'].sort());
    await navigate();
    assert.equal(vscode.window.activeTextEditor.document.uri.toString(), bomUri.toString());
    assert.equal(bomDoc.getText(vscode.window.activeTextEditor.selection), '😀x');
    await replace(bomDoc, 'B😀x\r\nZ');
    await eventually(() => api.request('denotate/originStatus', { uri: bomUri.toString() }), r => r.state === 'hash-mismatch', 'changed BOM buffer still wins over matching disk');
    await navigate();
    assert.equal(vscode.window.activeTextEditor.document.uri.toString(), checkedUri.toString());
    await replace(bomDoc, 'A😀x\r\nZ');
    await eventually(() => api.request('denotate/originStatus', { uri: bomUri.toString() }), r => r.state === 'matching' && r.snapshot.dirty, 'restored dirty BOM source matches again');
    await navigate();
    assert.equal(bomDoc.getText(vscode.window.activeTextEditor.selection), '😀x');
    await replace(checkedDoc, checkedText);

    // Stage 6 uses the actual rename provider and applies its versioned edits
    // over global syntax, contracts and origins. Uppercase constants stay quoted.
    await replace(checkedDoc, checkedText);
    const constantAt = checkedDoc.positionAt(checkedDoc.getText().indexOf('a,b:S'));
    const quotedRename = await vscode.commands.executeCommand('vscode.executeDocumentRenameProvider', checkedUri, constantAt, 'I');
    assert.ok(await vscode.workspace.applyEdit(quotedRename));
    assert.ok(checkedDoc.getText().includes("const 'I',b:S"));
    assert.ok(checkedDoc.getText().includes("p('I') loc(#s 1:1 to 1:6)"));
    assert.ok(checkedDoc.getText().includes(`hash:"${hash}"`));
    await eventually(conflicts, ds => ds.length === 2, 'quoted constant rename preserves checked conflict');
    const quotedAt = checkedDoc.positionAt(checkedDoc.getText().indexOf("'I',b:S"));
    const preparedQuoted = await api.request('textDocument/prepareRename', { textDocument: { uri: checkedUri.toString() }, position: quotedAt });
    assert.equal(preparedQuoted.placeholder, 'I');
    const quotedUndo = await vscode.commands.executeCommand('vscode.executeDocumentRenameProvider', checkedUri, quotedAt, 'a');
    assert.ok(await vscode.workspace.applyEdit(quotedUndo));
    assert.equal(checkedDoc.getText(), checkedText);
    const parameterAt = checkedDoc.positionAt(checkedText.indexOf('x:S'));
    const parameterRename = await vscode.commands.executeCommand('vscode.executeDocumentRenameProvider', checkedUri, parameterAt, 'column name');
    assert.ok(await vscode.workspace.applyEdit(parameterRename));
    assert.ok(checkedDoc.getText().includes("p('column name':S)"));
    await replace(checkedDoc, checkedText);

    // No implicit workspace root: create a standalone document outside the
    // existing root, then exercise both default and explicit destination creation.
    const temp = await require('node:fs/promises').mkdtemp(require('node:path').join(require('node:os').tmpdir(), 'denotate-root-smoke-'));
    const standaloneUri = vscode.Uri.file(require('node:path').join(temp, 'standalone.den'));
    await vscode.workspace.fs.writeFile(standaloneUri, Buffer.from('relation standalone(); standalone();'));
    const standalone = await vscode.workspace.openTextDocument(standaloneUri);
    await vscode.window.showTextDocument(standalone);
    await eventually(() => api.request('denotate/roots', { uri: standaloneUri.toString() }), r => r.state === 'standalone', 'no containing manifest');
    const fixes = await vscode.commands.executeCommand('vscode.executeCodeActionProvider', standaloneUri, new vscode.Range(0,0,0,0));
    assert.ok(fixes.some(f => f.title === 'Create den.root here'));
    await vscode.commands.executeCommand('denotate.createRoot', standaloneUri);
    const created = await eventually(() => api.request('denotate/roots', { uri: standaloneUri.toString() }), r => r.state === 'ready', 'create root in document folder');
    assert.equal(JSON.parse(Buffer.from(await vscode.workspace.fs.readFile(vscode.Uri.file(require('node:path').join(temp,'den.root')))).toString()).libraries, undefined);
    await vscode.commands.executeCommand('denotate.createRoot', standaloneUri);
    assert.equal(Buffer.from(await vscode.workspace.fs.readFile(vscode.Uri.file(require('node:path').join(temp,'den.root')))).toString(), '{}\n', 'existing manifest is not overwritten');
    const chosen = vscode.Uri.file(require('node:path').join(temp,'chosen'));
    await vscode.workspace.fs.createDirectory(chosen);
    await vscode.commands.executeCommand('denotate.createRoot', standaloneUri, chosen);
    assert.equal(Buffer.from(await vscode.workspace.fs.readFile(vscode.Uri.joinPath(chosen,'den.root'))).toString(), '{}\n');
    assert.ok(created.homeProgram.endsWith('/den.root'));
    // Referenced libraries outside the workspace receive real file watchers.
    const externalUri = vscode.Uri.joinPath(chosen, 'external.den');
    await vscode.workspace.fs.writeFile(externalUri, Buffer.from('namespace external; relation r();'));
    const libraryRelative = require('node:path').relative(folder.fsPath, vscode.Uri.joinPath(chosen,'den.root').fsPath);
    await replace(rootDoc, JSON.stringify({ libraries: [libraryRelative] }));
    const consumerUri = vscode.Uri.joinPath(folder, 'external-consumer.den');
    await vscode.workspace.fs.writeFile(consumerUri, Buffer.from('external::r();'));
    const consumer = await vscode.workspace.openTextDocument(consumerUri);
    await vscode.window.showTextDocument(consumer);
    await eventually(() => vscode.commands.executeCommand('vscode.executeDefinitionProvider', consumerUri, new vscode.Position(0,1)), refs => refs?.length === 1, 'external library loaded from dirty manifest');
    await vscode.workspace.fs.writeFile(externalUri, Buffer.from('namespace external; relation changed();'));
    await eventually(() => vscode.commands.executeCommand('vscode.executeDefinitionProvider', consumerUri, new vscode.Position(0,1)), refs => refs?.length === 0, 'external library watcher invalidates declarations');
    await vscode.workspace.fs.writeFile(externalUri, Buffer.from('namespace external; relation r();'));
    await eventually(() => vscode.commands.executeCommand('vscode.executeDefinitionProvider', consumerUri, new vscode.Position(0,1)), refs => refs?.length === 1, 'external library watcher repairs declarations');
    await replace(rootDoc, rootText);
    console.log('Denotate stage-6 smoke passed: validated quoted constant/parameter rename and checked round trip; Go to Origin on matching dirty buffers, changed-buffer refusal and Unicode/CRLF selections; checked dirty buffers and origin links; roots, dirty manifests, authoritative DSL buffers, quick fixes;  syntax/repair, outline, definition/completion, references, hover/signatures, applied cross-file rename round trip and idempotent formatting.');
};
