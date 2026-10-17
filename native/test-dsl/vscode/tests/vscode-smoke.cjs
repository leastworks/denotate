const assert = require('node:assert/strict');
const vscode = require('vscode');

function nextEvent(subscribe, accepts = () => true) {
    return new Promise((resolve, reject) => {
        const timer = setTimeout(() => {
            subscription.dispose();
            reject(new Error('Timed out waiting for InputMapping publication/checkpoint'));
        }, 15000);
        const subscription = subscribe(value => {
            if (!accepts(value)) return;
            clearTimeout(timer);
            subscription.dispose();
            resolve(value);
        });
    });
}

exports.run = async function () {
    const extension = vscode.extensions.getExtension('denotate.inputmapping-prototype');
    assert.ok(extension, 'InputMapping extension must be installed');
    const client = await extension.activate();
    const uri = vscode.Uri.joinPath(vscode.workspace.workspaceFolders[0].uri, 'overlap.inputmapping');
    const publications = new vscode.EventEmitter();
    // Observe actual converted diagnostics after the language client installs
    // them in VS Code, not just the server's wire-level messages.
    client.clientOptions.middleware.handleDiagnostics = (target, diagnostics, next) => {
        next(target, diagnostics);
        publications.fire({ uri: target.toString(), diagnostics: vscode.languages.getDiagnostics(target) });
    };
    const publication = () => nextEvent(publications.event, event => event.uri === uri.toString());
    const notification = method => nextEvent(listener => client.onNotification(method, listener),
        event => event.uri === uri.toString());
    let document;

    async function validUpdate(action) {
        // Force fast withdrawal and final checking to be separately observable.
        // In particular, an empty *fast* publication must not pass the repair test.
        await client.sendRequest('inputmapping/test/hold', { phase: 'afterPrepare' });
        const fast = publication();
        const ready = notification('denotate/test/frontendReady');
        const held = notification('inputmapping/test/checkpoint');
        await action();
        const [initial, parsed, checkpoint] = await Promise.all([fast, ready, held]);
        assert.deepEqual(initial.diagnostics, []);
        assert.equal(parsed.version, document.version);
        assert.equal(checkpoint.version, document.version);
        const final = publication();
        const validated = notification('denotate/test/validated');
        await client.sendRequest('inputmapping/test/release', { revision: checkpoint.revision });
        const [result, checked] = await Promise.all([final, validated]);
        assert.equal(checked.version, document.version);
        await client.sendRequest('denotate/test/idle');
        return result.diagnostics;
    }
    async function replace(text) {
        const edit = new vscode.WorkspaceEdit();
        edit.replace(uri, new vscode.Range(document.positionAt(0), document.positionAt(document.getText().length)), text);
        assert.equal(await vscode.workspace.applyEdit(edit), true);
        assert.equal(document.getText(), text);
    }
    function overlaps(diagnostics, shift = 0) {
        assert.equal(diagnostics.length, 2);
        for (const line of [4, 5]) {
            const diagnostic = diagnostics.find(item => item.range.start.line === line + shift);
            assert.ok(diagnostic, `diagnostic on mapping line ${line + shift}`);
            assert.equal(diagnostic.code, 'OverlappingMappings');
            assert.equal(diagnostic.source, 'InputMapping');
            assert.equal(diagnostic.severity, vscode.DiagnosticSeverity.Error);
            assert.equal(diagnostic.range.start.character, 0);
            assert.equal(diagnostic.range.end.line, line + shift);
            assert.equal(diagnostic.range.end.character, 1);
            assert.equal(document.getText(diagnostic.range), 'b');
            assert.match(diagnostic.message, /input_b, input_bb/);
            for (const [other, input] of [[4, 'input_b'], [5, 'input_bb']]) {
                const related = diagnostic.relatedInformation.find(item =>
                    item.location.uri.toString() === uri.toString()
                    && item.location.range.start.line === other + shift
                    && item.location.range.start.character === 5);
                assert.ok(related, `related Input occurrence ${input}`);
                assert.equal(document.getText(related.location.range), input);
            }
        }
    }

    try {
        const first = await validUpdate(async () => {
            document = await vscode.workspace.openTextDocument(uri);
            await vscode.window.showTextDocument(document);
        });
        assert.equal(document.languageId, 'inputmapping');
        assert.ok(extension.packageJSON.contributes.grammars.some(item =>
            item.language === 'inputmapping' && item.scopeName === 'source.inputmapping'));
        for (const feature of ['completionProvider', 'definitionProvider', 'renameProvider',
            'documentFormattingProvider', 'codeActionProvider']) {
            const capability = client.initializeResult.capabilities[feature];
            assert.ok(capability === undefined || capability === false, `${feature} is out of scope`);
        }
        const original = document.getText();
        overlaps(first);
        console.log('InputMapping: activation, both target ranges and related Input locations passed');

        const fixed = original.replace('slot a, b;', 'slot a, b, c;').replace('b <- input_bb', 'c <- input_bb');
        assert.deepEqual(await validUpdate(() => replace(fixed)), []);
        overlaps(await validUpdate(() => replace(original)));
        console.log('InputMapping: repair clears final findings; restoring the conflict restores both');

        assert.deepEqual(await validUpdate(() => replace(original + '\nmask b;\n')), []);
        overlaps(await validUpdate(() => replace(original)));
        console.log('InputMapping: masking clears the overlap; removal restores both exact target ranges');

        for (const [broken, code] of [
            [original.replace('input_bb when', 'when'), 'syntax'],
            [original.replace('available(a)', 'available(missing)'), 'name']
        ]) {
            const published = publication();
            const validated = notification('denotate/test/validated');
            await replace(broken);
            const [result, checked] = await Promise.all([published, validated]);
            assert.equal(checked.version, document.version);
            assert.equal(result.diagnostics.filter(d => d.code === 'paused').length, 1);
            assert.ok(result.diagnostics.some(d => d.code === code));
            assert.ok(result.diagnostics.every(d => d.code === code || d.code === 'paused'));
            overlaps(await validUpdate(() => replace(original)));
        }
        console.log('InputMapping: syntax/name errors pause checking; repair resumes it');

        overlaps(await validUpdate(() => replace('// comment\n' + original)), 1);
        const noMeaning = await validUpdate(() => replace(
            'input input_a;\nslot a;\na <- input_a when not available(a);\n'));
        const failure = noMeaning.find(d => d.code === 'NoMeaning');
        assert.ok(failure);
        assert.equal(failure.severity, vscode.DiagnosticSeverity.Error);
        assert.equal(document.getText(failure.range), 'not available(a)');
        assert.match(failure.message, /whenever input_a is present/);
        const masked = await validUpdate(() => replace('input i;\nslot a;\na <- i;\nmask a when available(a);\n'));
        const maskFailure = masked.find(d => d.code === 'NoMeaning');
        assert.ok(maskFailure);
        assert.equal(document.getText(maskFailure.range), 'available(a)');
        assert.match(maskFailure.message, /Masking Slot a depends on its own availability/);
        assert.ok(maskFailure.relatedInformation.some(r => document.getText(r.location.range) === 'a <- i;'));
        overlaps(await validUpdate(() => replace(original)));
        console.log('InputMapping: current ranges and no-meaning diagnostic passed');
    } finally {
        delete client.clientOptions.middleware.handleDiagnostics;
        publications.dispose();
        await client.stop();
    }
};
