const vscode = require('vscode');
const fs = require('node:fs/promises');
const path = require('node:path');
const { snapshotResolver, goToOrigin } = require('./origin-navigation.cjs');
const { LanguageClient } = require('vscode-languageclient/node');
let client;

exports.activate = async (context) => {
  client = new LanguageClient('denotate', 'Denotate',
    { command: context.asAbsolutePath(process.platform === 'win32' ? 'dist/denotate-lsp.exe' : 'dist/denotate-lsp'), args: [] },
    { documentSelector: [{ scheme: 'file', language: 'denotate' }], initializationOptions: { originSnapshotBridge: true } });
  context.subscriptions.push(client);
  const status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 20);
  context.subscriptions.push(status);
  let origins = new Set(), generation = 0, statusGeneration = 0, externalFolders = [];
  const rootWatchers = new Map(), originWatchers = new Map(), sourceGenerations = new Map();
  const canonical = (uri) => {
    if (uri.scheme !== 'file') return uri.toString();
    try { return require('node:fs').realpathSync(uri.fsPath); } catch { return uri.fsPath; }
  };
  const sameFile = (a, b) => canonical(a) === canonical(b);
  const isManifest = (uri) => uri.scheme === 'file' && path.basename(uri.fsPath) === 'den.root';
  const syncManifest = (document, closed = false) => {
    if (isManifest(document.uri)) return client.sendNotification('denotate/manifest', {
      uri: document.uri.toString(), closed, text: closed ? undefined : document.getText(), version: ++generation
    });
  };
  const originChanged = (uri) => {
    ++generation;
    sourceGenerations.set(canonical(uri), generation);
    return Promise.all([...origins].filter(value => sameFile(vscode.Uri.parse(value), uri)).map(value => client.sendNotification('denotate/originChanged', { uri: value, generation })));
  };
  const watch = (pattern, callback) => {
    const watcher = vscode.workspace.createFileSystemWatcher(pattern);
    for (const [event, type] of [['onDidCreate', 1], ['onDidChange', 2], ['onDidDelete', 3]]) watcher[event]((uri) => callback(uri, type));
    return watcher;
  };
  const memberEvent = async (uri, type) => {
    await originChanged(uri);
    await client.sendNotification('workspace/didChangeWatchedFiles', { changes: [{ uri: uri.toString(), type }] });
  };
  const refreshOriginWatchers = () => {
    const desired = new Map();
    for (const value of origins) {
      const uri = vscode.Uri.parse(value);
      if (uri.scheme !== 'file') continue;
      const covered = (uri.fsPath.endsWith('.den') || isManifest(uri)) && [...rootWatchers.keys()].some(folder => canonical(uri).startsWith(folder + path.sep));
      if (!covered) desired.set(value, new vscode.RelativePattern(vscode.Uri.file(path.dirname(uri.fsPath)), path.basename(uri.fsPath)));
    }
    for (const [key, watcher] of originWatchers) if (!desired.has(key)) { watcher.dispose(); originWatchers.delete(key); }
    for (const [key, pattern] of desired) if (!originWatchers.has(key)) originWatchers.set(key, watch(pattern, originChanged));
  };
  const refreshRootWatchers = (external = externalFolders) => {
    externalFolders = external;
    const folders = [...new Set([...(vscode.workspace.workspaceFolders || []).map(f => f.uri.fsPath), ...external.map(u => vscode.Uri.parse(u).fsPath)].map(folder => { while (!require('node:fs').existsSync(folder) && path.dirname(folder) !== folder) folder = path.dirname(folder); try { return require('node:fs').realpathSync(folder); } catch { return folder; } }))].sort((a,b) => a.length-b.length);
    const desired = folders.filter((folder, i) => !folders.slice(0,i).some(parent => folder === parent || folder.startsWith(parent + path.sep)));
    for (const [folder, watcher] of rootWatchers) if (!desired.includes(folder)) { watcher.dispose(); rootWatchers.delete(folder); }
    for (const folder of desired) if (!rootWatchers.has(folder)) rootWatchers.set(folder, watch(new vscode.RelativePattern(vscode.Uri.file(folder), '**/{*.den,den.root}'), memberEvent));
    refreshOriginWatchers();
  };
  const activeDocument = () => {
    const doc = vscode.window.activeTextEditor?.document;
    return doc?.languageId === 'denotate' && doc.uri.scheme === 'file' ? doc : undefined;
  };
  const refreshStatus = async () => {
    const ticket = ++statusGeneration, doc = activeDocument();
    if (!doc) { status.hide(); return; }
    const uri = doc.uri.toString();
    try {
      let result = await client.sendRequest('denotate/roots', { uri });
      if (ticket !== statusGeneration) return;
      const label = result.state === 'standalone' ? 'Standalone document'
        : result.homeProgram ? vscode.workspace.asRelativePath(vscode.Uri.parse(result.homeProgram))
        : 'Home program unavailable';
      const verifications = result.verifications;
      const outcomeState = result.state === 'invalid' ? 'invalid' : result.summary?.state ?? result.checking;
      const outcome = outcomeState === 'unconfigured' ? 'No verification configured' : outcomeState;
      const count = verifications ? `${verifications.length} verification${verifications.length === 1 ? '' : 's'}` : 'configuration incomplete';
      status.text = `Denotate: ${label} · ${count} · ${outcome}`;
      status.tooltip = [label, `${count}: ${outcome}`, `Checking: ${result.checking}`, `Backend: ${result.backend}`,
        ...(verifications ?? []).map(v => `${v.verification}: ${v.summary?.state ?? v.checking} (${v.checking}); assumptions [${v.assumptions.join(', ')}]; ${v.mode}; ${v.consistency}`),
        ...((verifications ?? []).some(v => v.mode === 'consistency-only') ? ['Consistency-only: no obligations selected; context-wide semantic diagnostics still run.'] : []),
        `Unchecked obligations: ${result.uncheckedObligations?.join(', ') || (verifications ? 'none' : 'configuration incomplete')}`,
        `Findings: ${result.findings?.length ?? 0}`, ...(result.originNotices ?? []).map(n => `Origin unavailable: ${n.uri} (${n.reason})`), ...result.errors].flat().join('\n');
      status.show();
    } catch (error) { if (ticket === statusGeneration) { status.text = 'Denotate: Root unavailable'; status.tooltip = String(error); status.show(); } }
  };
  const resolveOrigin = snapshotResolver(vscode, canonical, sourceGenerations);
  client.onRequest('denotate/originSnapshot', resolveOrigin);
  client.onNotification('denotate/originSubscriptions', ({ uris }) => { origins = new Set(uris); refreshOriginWatchers(); });
  client.onNotification('denotate/rootsChanged', ({ watchFolders }) => { refreshRootWatchers(watchFolders); void refreshStatus(); });
  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument(doc => { void syncManifest(doc); void originChanged(doc.uri); }),
    vscode.workspace.onDidChangeTextDocument(({ document }) => { void syncManifest(document); void originChanged(document.uri); }),
    vscode.workspace.onDidSaveTextDocument(doc => { void syncManifest(doc); void originChanged(doc.uri); }),
    vscode.workspace.onDidCloseTextDocument(doc => { void syncManifest(doc, true); void originChanged(doc.uri); }),
    vscode.window.onDidChangeActiveTextEditor(() => { void refreshStatus(); }),
    vscode.workspace.onDidChangeWorkspaceFolders(() => { refreshRootWatchers(); }),
    { dispose: () => { for (const watcher of [...rootWatchers.values(), ...originWatchers.values()]) watcher.dispose(); } },
    vscode.commands.registerCommand('denotate.goToOrigin', () => goToOrigin(vscode, (method, params) => client.sendRequest(method, params), resolveOrigin)),
    vscode.commands.registerCommand('denotate.createRoot', async (value, selectedFolder, chooseFolder = false) => {
      const uri = value ? vscode.Uri.parse(value.toString()) : activeDocument()?.uri; if (!uri) return;
      let folder = selectedFolder ? vscode.Uri.parse(selectedFolder.toString()) : vscode.Uri.file(path.dirname(uri.fsPath));
      if (chooseFolder) {
        const selected = await vscode.window.showOpenDialog({ canSelectFolders: true, canSelectFiles: false, canSelectMany: false });
        if (!selected?.length) return; folder = selected[0];
      }
      const target = vscode.Uri.joinPath(folder, 'den.root');
      if (vscode.workspace.textDocuments.some(d => d.uri.toString() === target.toString())) { void vscode.window.showErrorMessage('den.root is already open; it was not overwritten.'); return; }
      try { await fs.writeFile(target.fsPath, '{}\n', { flag: 'wx' }); }
      catch (error) { void vscode.window.showErrorMessage(`Could not create den.root: ${error.message}`); return; }
      await memberEvent(target, 1); await refreshStatus();
    })
  );
  await client.start();
  refreshRootWatchers();
  for (const doc of vscode.workspace.textDocuments) await syncManifest(doc);
  await refreshStatus();
  // Exposed to installed-extension smoke tests and other clients of this extension.
  return { request: (method, params) => client.sendRequest(method, params) };
};
exports.deactivate = async () => { await client?.stop(); };
