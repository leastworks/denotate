import { mkdtemp, cp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { runTests } from '@vscode/test-electron';

const vscodeExecutablePath = process.env.DENOTATE_VSCODE_EXECUTABLE;
if (!vscodeExecutablePath || !path.isAbsolute(vscodeExecutablePath)) {
    throw new Error('Set DENOTATE_VSCODE_EXECUTABLE to an absolute path to an installed VS Code.');
}
const extensionDevelopmentPath = fileURLToPath(new URL('..', import.meta.url));
const temporary = await mkdtemp(path.join(tmpdir(), 'denotate-b-vscode-'));
try {
    const workspace = path.join(temporary, 'workspace');
    await cp(fileURLToPath(new URL('../../fixtures/base/00-valid/', import.meta.url)), workspace, { recursive: true });
    await runTests({ vscodeExecutablePath, extensionDevelopmentPath,
        extensionTestsPath: path.join(extensionDevelopmentPath, 'dist/vscode-smoke.cjs'),
        extensionTestsEnv: { ELECTRON_RUN_AS_NODE: undefined, VSCODE_IPC_HOOK_CLI: undefined },
        launchArgs: [workspace, '--user-data-dir', path.join(temporary, 'profile'),
            '--extensions-dir', path.join(temporary, 'extensions'), '--disable-extensions',
            '--disable-workspace-trust', '--skip-welcome', '--skip-release-notes', '--disable-updates'] });
} finally {
    // Only this freshly created temporary editor profile/workspace is removed.
    await rm(temporary, { recursive: true, force: true });
}
