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
    console.log('Denotate B2 smoke passed: syntax/repair, outline, imported definition and typed completion through Rust/Salsa.');
};
