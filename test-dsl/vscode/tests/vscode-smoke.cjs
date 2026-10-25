const assert = require('node:assert/strict');
const vscode = require('vscode');

function nextEvent(subscribe, accepts = () => true) {
    return new Promise((resolve, reject) => {
        const timer = setTimeout(() => {
            subscription.dispose();
            reject(new Error('Timed out waiting for the test DSL publication/checkpoint'));
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
    const extension = vscode.extensions.getExtension('denotate.denotate-test-dsl');
    assert.ok(extension, 'The test DSL extension must be installed');
    const client = await extension.activate();
    const uri = vscode.Uri.joinPath(vscode.workspace.workspaceFolders[0].uri, 'overlap.testdsl');
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
        await client.sendRequest('denotate/test/hold', { phase: 'duringCheck' });
        const fast = publication();
        const ready = notification('denotate/test/frontendReady');
        const held = notification('denotate/test/checkpoint');
        await action();
        const [initial, parsed, checkpoint] = await Promise.all([fast, ready, held]);
        assert.deepEqual(initial.diagnostics, []);
        assert.equal(parsed.version, document.version);
        assert.equal(checkpoint.version, document.version);
        const final = publication();
        const validated = notification('denotate/test/validated');
        await client.sendRequest('denotate/test/release', { revision: checkpoint.revision });
        const [result, checked] = await Promise.all([final, validated]);
        assert.equal(checked.version, document.version);
        await client.sendRequest('denotate/test/checkingIdle');
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
            assert.equal(diagnostic.source, 'test DSL');
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
        assert.equal(document.languageId, 'testdsl');
        assert.ok(extension.packageJSON.contributes.grammars.some(item =>
            item.language === 'testdsl' && item.scopeName === 'source.testdsl'));
        for (const feature of ['completionProvider', 'definitionProvider', 'renameProvider',
            'documentFormattingProvider', 'codeActionProvider']) {
            const capability = client.initializeResult.capabilities[feature];
            assert.ok(capability === undefined || capability === false, `${feature} is out of scope`);
        }
        const original = document.getText();
        overlaps(first);
        console.log('Test DSL: activation, both target ranges and related Input locations passed');

        const fixed = original.replace('slot a, b;', 'slot a, b, c;').replace('b <- input_bb', 'c <- input_bb');
        assert.deepEqual(await validUpdate(() => replace(fixed)), []);
        overlaps(await validUpdate(() => replace(original)));
        console.log('Test DSL: repair clears final findings; restoring the conflict restores both');

        assert.deepEqual(await validUpdate(() => replace(original + '\nmask b;\n')), []);
        overlaps(await validUpdate(() => replace(original)));
        console.log('Test DSL: masking clears the overlap; removal restores both exact target ranges');

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
        console.log('Test DSL: syntax/name errors pause checking; repair resumes it');

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
        const valueConflict = 'input i, j;\nslot a;\na <- i when input_value(i) is 1;\na <- j when input_value(j) is 1;\n';
        const valueDiagnostics = await validUpdate(() => replace(valueConflict));
        assert.equal(valueDiagnostics.filter(d => d.code === 'OverlappingMappings').length, 2);
        const valueWarning = await validUpdate(() => replace(
            'input i; slot a; a <- i when input_value(i) is 1 and not (input_value(i) is 2);'));
        const redundant = valueWarning.find(d => d.code === 'redundant');
        assert.ok(redundant);
        assert.equal(document.getText(redundant.range), 'not (input_value(i) is 2)');
        assert.match(redundant.message, /cannot also have value 2/);
        const published = publication();
        const validated = notification('denotate/test/validated');
        await replace('input i; slot a; a <- i when input_value(i) is 9223372036854775808;');
        const [invalid] = await Promise.all([published, validated]);
        const literal = invalid.diagnostics.find(d => d.code === 'literal');
        assert.ok(literal);
        assert.equal(document.getText(literal.range), '9223372036854775808');
        assert.ok(invalid.diagnostics.every(d => d.code === 'literal' || d.code === 'paused'));
        overlaps(await validUpdate(() => replace(original)));
        console.log('Test DSL: current ranges, no-meaning, value guards and overflow repair passed');
    } finally {
        delete client.clientOptions.middleware.handleDiagnostics;
        publications.dispose();
        await client.stop();
    }
};
