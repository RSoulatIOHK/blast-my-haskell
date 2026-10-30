// Uses an installed VS Code executable. All profile, extension, and source data
// lives in a disposable directory; the user's VS Code session is untouched.
const fs = require('node:fs/promises');
const path = require('node:path');
const os = require('node:os');
const { spawn } = require('node:child_process');
(async () => {
  const extension = path.resolve(__dirname, '..'), repo = path.dirname(extension);
  const temporary = await fs.mkdtemp(path.join(os.tmpdir(), 'ghccore-editor-host-'));
  let success = false;
  try {
    const workspace = path.join(temporary, 'workspace');
    const profile = path.join(temporary, 'profile');
    await fs.mkdir(workspace); await fs.mkdir(path.join(profile, 'User'), { recursive: true });
    for (const name of ['PureInteger', 'SmtInteger', 'Admitted']) {
      await fs.copyFile(path.join(repo, 'tests/fixtures/verification', name + '.hs'), path.join(workspace, name + '.hs'));
    }
    await fs.writeFile(path.join(profile, 'User/settings.json'), JSON.stringify({
      'ghcCoreLean.verifyScriptPath': path.join(repo, 'verify.sh'),
      'workbench.startupEditor': 'none', 'telemetry.telemetryLevel': 'off',
      'update.mode': 'none', 'extensions.autoUpdate': false,
    }));
    let code = process.env.VSCODE_EXECUTABLE || 'code';
    if (!process.env.VSCODE_EXECUTABLE && process.platform === 'darwin') {
      // Run Electron directly so its exit code is the test runner's exit code,
      // not the macOS `code` launcher forwarding to an application instance.
      for (const bin of (process.env.PATH ?? '').split(path.delimiter)) {
        try {
          const cli = await fs.realpath(path.join(bin, 'code'));
          const suffix = '/Contents/Resources/app/bin/code';
          if (cli.endsWith(suffix)) { code = cli.slice(0, -suffix.length) + '/Contents/MacOS/Code'; break; }
        } catch { /* Continue searching PATH. */ }
      }
    }
    const env = { ...process.env };
    for (const key of Object.keys(env)) {
      if (key.startsWith('VSCODE_') || key === 'ELECTRON_RUN_AS_NODE') delete env[key];
    }
    const proc = spawn(code, [workspace, '--new-window', '--wait', '--disable-extensions',
      '--disable-workspace-trust', '--skip-welcome', '--skip-release-notes',
      '--user-data-dir', profile, '--extensions-dir', path.join(temporary, 'extensions'),
      '--extensionDevelopmentPath=' + extension, '--extensionTestsPath=' + path.join(__dirname, 'host-smoke.cjs')],
      { stdio: 'inherit', env });
    const result = await new Promise((resolve, reject) => {
      proc.on('error', reject); proc.on('close', code => resolve(code));
    });
    if (result !== 0) throw new Error(`Extension host exited ${result}`);
    const evidence = JSON.parse(await fs.readFile(path.join(temporary, 'host-result.json'), 'utf8'));
    if (evidence.passed?.length !== 3) throw new Error('Extension host did not complete all smoke checks');
    console.log('Extension host checks passed:', JSON.stringify(evidence));
    success = true;
  } finally {
    if (success) await fs.rm(temporary, { recursive: true, force: true });
    else console.error('Extension host failure logs retained in:', temporary);
  }
})().catch(error => { console.error(error); process.exitCode = 1; });
