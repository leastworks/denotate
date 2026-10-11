const { LanguageClient } = require('vscode-languageclient/node');
let client;

exports.activate = async function (context) {
    const executable = context.asAbsolutePath(process.platform === 'win32'
        ? 'dist/denotate-lsp.exe' : 'dist/denotate-lsp');
    // One language server at a time. No Node host/native bridge inside B.
    client = new LanguageClient('denotate-tree-sitter', 'Denotate IR (Tree-sitter)',
        { command: executable, args: [] },
        { documentSelector: [{ scheme: 'file', language: 'denotate' }] });
    context.subscriptions.push(client);
    await client.start();
};
exports.deactivate = async function () { await client?.stop(); };
