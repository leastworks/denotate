const { LanguageClient } = require('vscode-languageclient/node');

let client;
exports.activate = async function (context) {
    const suffix = process.platform === 'win32' ? '.exe' : '';
    client = new LanguageClient('testdsl', 'Denotate test DSL',
        { command: context.asAbsolutePath(`dist/test-dsl-lsp${suffix}`), args: [] },
        { documentSelector: [{ scheme: 'file', language: 'testdsl' }] });
    context.subscriptions.push(client);
    await client.start();
    // The editor smoke uses the existing test protocol through this client.
    // Normal activation adds no commands or test-only server behavior.
    return client;
};
exports.deactivate = async function () {
    await client?.stop();
};
