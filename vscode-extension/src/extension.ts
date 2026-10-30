import * as vscode from 'vscode';
import * as cp from 'child_process';
import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';
import { promisify } from 'util';
import { createHash } from 'crypto';
import { Block, ModuleResult, Policy, Report, Status, Tone, presentation } from './protocol';
import { RunError, RunGate, runVerifier } from './runner';

const channel = vscode.window.createOutputChannel('GHC Core → Lean');
const diagnostics = vscode.languages.createDiagnosticCollection('ghccoretolean');
const codeLensEmitter = new vscode.EventEmitter<void>();
const gate = new RunGate();
let request = 0;
let shuttingDown = false;
let savedInputs = new Map<string, string>();
let resultWatchers: vscode.Disposable[] = [];
interface Annotation { range: vscode.Range; label: string; detail: string; tone: Tone }
const annotations = new Map<string, Annotation[]>();
const decorations = new Map<Tone, vscode.TextEditorDecorationType>();
for (const [tone, icon, color] of [
  ['success', 'pass.svg', 'rgba(46, 204, 113, 0.7)'],
  ['warning', 'warning.svg', 'rgba(230, 170, 40, 0.7)'],
  ['failure', 'fail.svg', 'rgba(231, 76, 60, 0.7)'],
] as const) {
  decorations.set(tone, vscode.window.createTextEditorDecorationType({
    gutterIconPath: vscode.Uri.file(path.join(__dirname, '..', 'media', icon)),
    gutterIconSize: 'contain', overviewRulerColor: color,
    overviewRulerLane: vscode.OverviewRulerLane.Right,
  }));
}

function markdown(detail: string): vscode.MarkdownString {
  const md = new vscode.MarkdownString();
  md.appendCodeblock(detail, 'text');
  md.isTrusted = false;
  return md;
}
function applyDecorations(editor: vscode.TextEditor): void {
  const entries = annotations.get(editor.document.uri.toString()) ?? [];
  for (const [tone, decoration] of decorations) {
    editor.setDecorations(decoration, entries.filter(a => a.tone === tone).map(a => ({
      range: new vscode.Range(a.range.start.line, 0, a.range.start.line, 0),
      hoverMessage: markdown(a.detail),
    })));
  }
}
function clearResults(): void {
  diagnostics.clear(); annotations.clear(); codeLensEmitter.fire();
  resultWatchers.forEach(w => w.dispose()); resultWatchers = [];
  vscode.window.visibleTextEditors.forEach(applyDecorations);
}
function invalidate(reason?: string): void {
  gate.invalidate(); clearResults();
  if (reason) channel.appendLine(reason);
}
function isHaskell(uri: vscode.Uri): boolean { return uri.scheme === 'file' && uri.fsPath.endsWith('.hs'); }
function sourceChanged(uri: vscode.Uri): void {
  if (!shuttingDown && isHaskell(uri)) invalidate('Haskell inputs changed; previous results cleared. Run Verify again.');
}
async function diskChanged(uri: vscode.Uri): Promise<void> {
  if (shuttingDown || !isHaskell(uri)) return;
  const generation = gate.version;
  let unchanged = false;
  try {
    const source = await fs.promises.realpath(uri.fsPath);
    const hash = createHash('sha256').update(await fs.promises.readFile(source)).digest('hex');
    unchanged = savedInputs.get(source) === hash;
  } catch { /* Deleted or unreadable inputs invalidate results too. */ }
  // Filesystem notifications can arrive after a save and after the next run
  // starts. A notification for the bytes we just staged must not cancel it.
  if (gate.current(generation) && !unchanged) sourceChanged(uri);
}
function settings(uri: vscode.Uri): Policy & { script: string; cwd: string; timeoutSeconds: number } {
  const cfg = vscode.workspace.getConfiguration('ghcCoreLean', uri);
  const cwd = vscode.workspace.getWorkspaceFolder(uri)?.uri.fsPath;
  if (!cwd) throw new RunError('error', 'Open the Haskell project in a workspace folder first.');
  const configured = cfg.get<string>('verifyScriptPath', 'verify.sh');
  const semantics = cfg.get<string>('semantics', 'conservative');
  if (semantics !== 'conservative' && semantics !== 'approximate') throw new RunError('error', 'Invalid semantic policy.');
  return { script: path.resolve(cwd, configured), cwd, semantics,
    trustSmt: cfg.get<boolean>('trustSmt', false), timeoutSeconds: cfg.get<number>('timeoutSeconds', 600) };
}
function blockRange(doc: vscode.TextDocument, hs: [number, number]): vscode.Range {
  if (hs[1] > doc.lineCount) throw new RunError('stale', 'Source ranges no longer match the document.');
  return new vscode.Range(hs[0] - 1, 0, hs[1] - 1, doc.lineAt(hs[1] - 1).text.length);
}
function severity(tone: Tone): vscode.DiagnosticSeverity {
  return tone === 'failure' ? vscode.DiagnosticSeverity.Error :
    tone === 'warning' ? vscode.DiagnosticSeverity.Warning : vscode.DiagnosticSeverity.Information;
}
function putSummary(doc: vscode.TextDocument, label: string, detail: string, tone: Tone): void {
  const d = new vscode.Diagnostic(new vscode.Range(0, 0, 0, doc.lineAt(0).text.length),
    `${label}\n${detail}`, severity(tone));
  d.source = 'GHC Core → Lean'; diagnostics.set(doc.uri, [...(diagnostics.get(doc.uri) ?? []), d]);
}
function diagnosticText(module: ModuleResult, block?: Block): string {
  return module.diagnostics.filter(d => !d.data.startsWith('GHCCORE_AUDIT:') &&
    (!block || (d.pos && d.pos.line >= block.lean[0] && d.pos.line <= block.lean[1])))
    .map(d => d.data).join('\n');
}
function reportDetail(report: Report): string {
  return `Run ${report.runId}\n${report.semantics} semantics; SMT trust ${report.trustSmt ? 'enabled' : 'disabled'}; ` +
    `run accepted: ${report.accepted}\nTranslation from Haskell to Lean is not certified.\n` +
    (report.detail ?? '');
}

function publish(report: Report, docs: Map<string, vscode.TextDocument>, entry: vscode.TextDocument): void {
  const context = reportDetail(report);
  for (const module of report.modules) {
    const doc = docs.get(module.source)!;
    const entries: Annotation[] = [];
    const diags: vscode.Diagnostic[] = [];
    for (const block of module.sourceMap.blocks) {
      const prop = module.properties.find(p => p.hs[0] === block.hs[0] && p.hs[1] === block.hs[1]);
      const text = diagnosticText(module, block);
      // Failed modules have no audited properties. Only the block with the
      // refutation diagnostic is labelled refuted; other blocks remain unchecked.
      const state: Status = prop?.status ??
        (module.status === 'refuted' && text.includes('Goal was falsified') ? 'refuted' : 'error');
      const view = presentation(state, report);
      const label = !prop && state !== 'refuted' ? 'Not verified · module failed' : view.label;
      const detail = [label, context, ...(prop?.theorems ?? []).map(t =>
        `${t.name}: ${t.status}\nAxioms: ${t.axioms.join(', ') || 'none'}`), text].filter(Boolean).join('\n\n');
      const range = blockRange(doc, block.hs);
      entries.push({ range, label, detail, tone: view.tone });
      if (view.tone !== 'success') {
        const d = new vscode.Diagnostic(range, label, severity(view.tone));
        d.source = 'GHC Core → Lean'; diags.push(d);
      }
    }
    // Preserve every compiler/solver error, including errors outside annotations.
    for (const d of module.diagnostics) {
      if (d.severity !== 'error' && d.severity !== 'warning') continue;
      const block = module.sourceMap.blocks.find(b => d.pos && d.pos.line >= b.lean[0] && d.pos.line <= b.lean[1]);
      const line = block && d.pos ? Math.min(block.hs[1] - 1, block.hs[0] + d.pos.line - block.lean[0]) : 0;
      const range = new vscode.Range(line, 0, line, doc.lineAt(line).text.length);
      const diag = new vscode.Diagnostic(range, d.data,
        d.severity === 'error' ? vscode.DiagnosticSeverity.Error : vscode.DiagnosticSeverity.Warning);
      diag.source = block ? 'Lean' : 'Lean (generated code)'; diags.push(diag);
    }
    annotations.set(doc.uri.toString(), entries); diagnostics.set(doc.uri, diags);
    if (module.stderr || module.detail || module.warnings) {
      putSummary(doc, presentation(module.status, report).label,
        [module.detail, module.stderr, module.warnings].filter(Boolean).join('\n'),
        module.status === 'error' ? 'failure' : 'warning');
    }
  }
  const view = presentation(report.status, report);
  if (!report.accepted) putSummary(entry, view.label, context, view.tone);
  codeLensEmitter.fire(); vscode.window.visibleTextEditors.forEach(applyDecorations);
  channel.appendLine(`${view.label}; accepted=${report.accepted}; ${report.elapsedSeconds}s`);
  if (report.detail) channel.appendLine(report.detail);
  const reason = report.status === 'unsupported' && report.detail?.includes('[machine-number]')
    ? ' Conservative semantics refuses machine numeric types such as Haskell Int. See ghcCoreLean.semantics in Settings.' : '';
  void vscode.window.showInformationMessage(`GHC Core → Lean: ${view.label}; run ${report.accepted ? 'accepted' : 'not accepted'}.${reason}`);
}

async function verify(): Promise<void> {
  const doc = vscode.window.activeTextEditor?.document;
  if (!doc || !isHaskell(doc.uri)) {
    void vscode.window.showWarningMessage('Open a saved .hs file first.'); return;
  }
  if (!vscode.workspace.isTrusted) return;
  const ticket = ++request;
  invalidate(); channel.show(true);
  channel.appendLine(`Starting verification of ${doc.fileName}…`);
  let generation: number | undefined;
  try {
    if (doc.isDirty && !await doc.save()) throw new RunError('error', 'Could not save the active Haskell file.');
    if (ticket !== request) return;
    if (vscode.workspace.textDocuments.some(d => isHaskell(d.uri) && d.isDirty)) {
      throw new RunError('error', 'Save the other modified Haskell documents before verification so imports match the editor.');
    }
    const config = settings(doc.uri);
    const source = await fs.promises.realpath(doc.uri.fsPath);
    const snapshots = new Map<string, string>();
    for (const open of vscode.workspace.textDocuments.filter(d => isHaskell(d.uri))) {
      try {
        const input = await fs.promises.realpath(open.uri.fsPath);
        snapshots.set(input, createHash('sha256').update(await fs.promises.readFile(input)).digest('hex'));
      } catch { /* Unrelated missing documents are not staged CLI inputs. */ }
    }
    if (ticket !== request) return;
    if (vscode.workspace.textDocuments.some(d => isHaskell(d.uri) && d.isDirty)) {
      throw new RunError('stale', 'A Haskell document changed; save it and verify again.');
    }
    savedInputs = snapshots;
    const run = gate.begin(); generation = run.generation;
    const report = await vscode.window.withProgress({ location: vscode.ProgressLocation.Notification,
      title: `GHC Core → Lean: verifying (${config.semantics})…`, cancellable: true },
    async (progress, token) => {
      const started = Date.now();
      let phase = 'Starting verifier';
      const update = () => {
        if (gate.current(run.generation)) progress.report({ message: `${phase} · ${Math.floor((Date.now() - started) / 1000)}s elapsed` });
      };
      update();
      const heartbeat = setInterval(update, 1000);
      const outputHeartbeat = setInterval(() => {
        if (gate.current(run.generation) && !shuttingDown) {
          channel.appendLine(`${phase} — still running (${Math.floor((Date.now() - started) / 1000)}s elapsed).`);
        }
      }, 15000);
      const sub = token.onCancellationRequested(() => {
        if (gate.current(run.generation)) {
          invalidate('Verification cancelled.');
          void vscode.window.showInformationMessage('GHC Core → Lean: verification cancelled.');
        }
      });
      try {
        if (token.isCancellationRequested) throw new RunError('cancelled', 'Verification cancelled.');
        return await runVerifier({ ...config, source, signal: run.signal,
          log: message => { if (!shuttingDown) channel.appendLine(message); },
          onProgress: message => {
            if (!gate.current(run.generation) || shuttingDown) return;
            phase = message; channel.appendLine(message + '…'); update();
          } });
      } finally { clearInterval(heartbeat); clearInterval(outputHeartbeat); sub.dispose(); }
    });
    if (!gate.current(run.generation)) return;
    if (report.status === 'stale' || report.status === 'cancelled' || report.status === 'timeout') {
      throw new RunError(report.status, report.detail ?? presentation(report.status, report).label);
    }
    // Watch imported sources too, including imports outside workspace folders.
    for (const dir of new Set(report.modules.map(m => path.dirname(m.source)))) {
      const watcher = vscode.workspace.createFileSystemWatcher(new vscode.RelativePattern(dir, '*.hs'));
      resultWatchers.push(watcher, watcher.onDidChange(diskChanged),
        watcher.onDidCreate(diskChanged), watcher.onDidDelete(diskChanged));
    }
    const docs = new Map<string, vscode.TextDocument>();
    const openByPath = new Map<string, vscode.TextDocument>();
    for (const open of vscode.workspace.textDocuments.filter(d => isHaskell(d.uri))) {
      try { openByPath.set(await fs.promises.realpath(open.uri.fsPath), open); }
      catch { /* A deleted unrelated document is not a verified input. */ }
    }
    // The CLI resolves symlinks; editor URIs need not. Keep the original entry
    // URI (e.g. macOS /var versus /private/var) for decorations and diagnostics.
    openByPath.set(source, doc);
    for (const module of report.modules) {
      const loaded = openByPath.get(module.source) ?? await vscode.workspace.openTextDocument(vscode.Uri.file(module.source));
      const hash = createHash('sha256').update(await fs.promises.readFile(module.source)).digest('hex');
      if (loaded.isDirty || hash !== module.sha256) throw new RunError('stale', 'A Haskell source changed; verify again.');
      savedInputs.set(module.source, hash);
      // Validate ranges before publishing any part of a result.
      module.sourceMap.blocks.forEach(b => blockRange(loaded, b.hs));
      docs.set(module.source, loaded);
    }
    if (!gate.current(run.generation)) return;
    if (vscode.workspace.textDocuments.some(d => isHaskell(d.uri) && d.isDirty)) {
      throw new RunError('stale', 'A Haskell document changed; verify again.');
    }
    publish(report, docs, doc);
  } catch (error) {
    if (ticket !== request || (generation !== undefined && !gate.current(generation))) return;
    clearResults();
    const failure = error instanceof RunError ? error : new RunError('error', (error as Error).message);
    channel.appendLine(`${failure.status}: ${failure.message}`);
    putSummary(doc, failure.status, failure.message, failure.status === 'error' ? 'failure' : 'warning');
    void vscode.window.showWarningMessage(`GHC Core → Lean: ${failure.message}`);
  } finally { if (generation !== undefined) gate.finish(generation); }
}

const execFile = promisify(cp.execFile);
async function checkEnvironment(): Promise<void> {
  const uri = vscode.window.activeTextEditor?.document.uri ?? vscode.workspace.workspaceFolders?.[0]?.uri;
  if (!uri) { void vscode.window.showWarningMessage('Open the project workspace first.'); return; }
  channel.show(true);
  try {
    const config = settings(uri);
    const repo = path.dirname(config.script);
    const env = { ...process.env, PATH: [
      '.ghcup/bin', '.cabal/bin', '.elan/bin', '.local/bin',
    ].map(p => path.join(os.homedir(), p)).concat(['/opt/homebrew/bin', '/usr/local/bin', process.env.PATH ?? '']).join(path.delimiter) };
    channel.appendLine(`Environment for ${config.script}`);
    let ok = fs.existsSync(config.script);
    channel.appendLine(`${ok ? '✓' : '✗'} verify script: ${config.script}`);
    for (const [command, args, cwd] of [
      ['python3', ['--version'], repo], ['lean', ['--version'], repo],
      ['ghc-9.2.7', ['--version'], repo], ['cabal', ['--version'], repo],
      ['cabal', ['list-bin', 'exe:ghc-core-shim'], path.join(repo, 'shim')],
    ] as [string, string[], string][]) {
      try {
        const result = await execFile(command, args, { cwd, env, timeout: 10000 });
        const value = result.stdout.trim();
        if (args[0] === 'list-bin' && !fs.existsSync(value)) throw new Error('shim is not built');
        channel.appendLine(`✓ ${command} ${args.join(' ')}: ${value}`);
      } catch (error) { ok = false; channel.appendLine(`✗ ${command}: ${(error as Error).message}`); }
    }
    for (const relative of ['.lake/build/bin/ghccoretolean',
      '.lake/build/lib/lean/GhcCoreToLean/Runtime.olean', '.lake/build/lib/lean/GhcCoreToLean/Audit.olean']) {
      const exists = fs.existsSync(path.join(repo, relative)); ok = ok && exists;
      channel.appendLine(`${exists ? '✓' : '✗'} ${relative}`);
    }
    channel.appendLine('Build in the repository: lake build GhcCoreToLean ghccoretolean && (cd shim && cabal build)');
    channel.appendLine('Blaster proofs additionally require Z3 on the verifier PATH. Run Verify to check the complete toolchain.');
    void vscode.window.showInformationMessage(ok ? 'GHC Core → Lean: prerequisites found.' : 'GHC Core → Lean: missing prerequisites; see output.');
  } catch (error) { void vscode.window.showWarningMessage((error as Error).message); }
}

export function activate(ctx: vscode.ExtensionContext): void {
  shuttingDown = false;
  const watcher = vscode.workspace.createFileSystemWatcher('**/*.hs');
  ctx.subscriptions.push(channel, diagnostics, codeLensEmitter, ...decorations.values(), watcher,
    { dispose: deactivate },
    vscode.commands.registerCommand('ghcCoreLean.verify', verify),
    vscode.commands.registerCommand('ghcCoreLean.clearDiagnostics', () => { request++; invalidate('Cleared verification results.'); }),
    vscode.commands.registerCommand('ghcCoreLean.checkEnvironment', checkEnvironment),
    vscode.commands.registerCommand('ghcCoreLean.showOutput', () => channel.show(true)),
    vscode.languages.registerHoverProvider({ language: 'haskell', scheme: 'file' }, {
      provideHover(doc, pos) {
        const entry = annotations.get(doc.uri.toString())?.find(a => a.range.contains(pos));
        return entry ? new vscode.Hover(markdown(entry.detail), entry.range) : undefined;
      },
    }),
    vscode.languages.registerCodeLensProvider({ language: 'haskell', scheme: 'file' }, {
      onDidChangeCodeLenses: codeLensEmitter.event,
      provideCodeLenses(doc) {
        return (annotations.get(doc.uri.toString()) ?? []).map(a => new vscode.CodeLens(
          new vscode.Range(a.range.start.line, 0, a.range.start.line, 0),
          { title: `${a.tone === 'success' ? '✓' : a.tone === 'failure' ? '✗' : '⚠'} ${a.label}`,
            command: 'ghcCoreLean.showOutput' }));
      },
    }),
    vscode.window.onDidChangeVisibleTextEditors(editors => editors.forEach(applyDecorations)),
    vscode.workspace.onDidChangeTextDocument(e => { if (e.contentChanges.length) sourceChanged(e.document.uri); }),
    watcher.onDidChange(diskChanged), watcher.onDidCreate(diskChanged), watcher.onDidDelete(diskChanged),
    vscode.workspace.onDidChangeConfiguration(e => {
      if (e.affectsConfiguration('ghcCoreLean')) { request++; invalidate('Verification settings changed; verify again.'); }
    }),
  );
}
export function deactivate(): void {
  shuttingDown = true;
  request++; gate.invalidate(); resultWatchers.forEach(w => w.dispose()); resultWatchers = [];
}
