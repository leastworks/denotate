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
    console.log('Denotate B3 smoke passed: syntax/repair, outline, definition/completion, references, hover/signatures, applied cross-file rename round trip and idempotent formatting.');
};
