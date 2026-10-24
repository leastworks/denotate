const assert = require('node:assert/strict');
const vscode = require('vscode');

exports.run = async function () {
    const extension = vscode.extensions.getExtension('denotate.denotate-tree-sitter-prototype');
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
    console.log('Denotate stage-2 smoke passed: roots, dirty manifests, authoritative DSL buffers, quick fixes;  syntax/repair, outline, definition/completion, references, hover/signatures, applied cross-file rename round trip and idempotent formatting.');
};
