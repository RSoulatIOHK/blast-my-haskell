import * as vscode from 'vscode';
import * as cp from 'child_process';
import * as fs from 'fs';
import * as path from 'path';

interface Block { hs: [number, number]; lean: [number, number] }
interface SourceMap {
  haskellPath: string;
  leanPath: string;
  blocks: Block[];
}

const channel = vscode.window.createOutputChannel('GHC Core → Lean');
const diagCol = vscode.languages.createDiagnosticCollection('ghccoretolean');

// Cache of "rich" per-block messages keyed by .hs URI then "startLine-endLine".
// Used by the hover provider to render the full Lean diagnostic text
// (incl. counterexamples) even when the inline diagnostic shows a short label.
const richMessages = new Map<string, Map<string, string>>();

function getScriptPath(): string {
  const cfg = vscode.workspace.getConfiguration('ghcCoreLean');
  const configured = cfg.get<string>('scriptPath') ?? 'transpile.sh';
  if (path.isAbsolute(configured)) return configured;
  const ws = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
  if (!ws) throw new Error('No workspace folder open.');
  return path.join(ws, configured);
}

function runPipeline(hsPath: string): Promise<string> {
  const ws = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath ?? path.dirname(hsPath);
  return new Promise((resolve, reject) => {
    const proc = cp.spawn('bash', [getScriptPath(), hsPath], { cwd: ws });
    let stdout = '';
    let stderr = '';
    proc.stdout.on('data', (d) => (stdout += d.toString()));
    proc.stderr.on('data', (d) => (stderr += d.toString()));
    proc.on('error', (err) => reject(err));
    proc.on('exit', (code) => {
      channel.appendLine(`--- transpile.sh ${path.basename(hsPath)} (exit ${code}) ---`);
      if (stdout) channel.appendLine(stdout);
      if (stderr) channel.appendLine(stderr);
      if (code !== 0) {
        reject(new Error(`transpile.sh exit ${code}: ${stderr || stdout}`));
        return;
      }
      // The script prints "wrote /path/to/out.lean" — parse out the path.
      const m = /wrote (\S+\.lean)/.exec(stdout);
      if (m) resolve(m[1]);
      else reject(new Error('transpile.sh succeeded but did not report an output path.'));
    });
  });
}

function readSourceMap(leanPath: string): SourceMap | null {
  const mapPath = `${leanPath}.map.json`;
  if (!fs.existsSync(mapPath)) return null;
  try {
    return JSON.parse(fs.readFileSync(mapPath, 'utf8')) as SourceMap;
  } catch (e) {
    channel.appendLine(`Failed to parse ${mapPath}: ${(e as Error).message}`);
    return null;
  }
}

/** Wait for the Lean LSP to publish a stable set of diagnostics for `uri`.
 *  Resolves once the diagnostic stream has been quiet for `quietMs`, or
 *  `totalMs` has elapsed overall. */
function waitForLeanDiagnostics(
  uri: vscode.Uri,
  quietMs: number,
  totalMs: number,
): Promise<vscode.Diagnostic[]> {
  return new Promise((resolve) => {
    const start = Date.now();
    let lastChange = Date.now();

    const sub = vscode.languages.onDidChangeDiagnostics((e) => {
      if (e.uris.some((u) => u.toString() === uri.toString())) {
        lastChange = Date.now();
      }
    });

    const tick = () => {
      const now = Date.now();
      const quiet = now - lastChange >= quietMs;
      const timedOut = now - start >= totalMs;
      if (quiet || timedOut) {
        sub.dispose();
        resolve(vscode.languages.getDiagnostics(uri));
      } else {
        setTimeout(tick, 250);
      }
    };
    setTimeout(tick, quietMs);
  });
}

async function verify(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!editor) {
    vscode.window.showWarningMessage('Open a .hs file first.');
    return;
  }
  const doc = editor.document;
  if (!doc.fileName.endsWith('.hs')) {
    vscode.window.showWarningMessage(`Active file is not Haskell: ${doc.fileName}`);
    return;
  }

  channel.show(true);
  await doc.save();

  let leanPath: string;
  try {
    leanPath = await vscode.window.withProgress(
      { location: vscode.ProgressLocation.Notification, title: 'GHC Core → Lean: transpiling…' },
      () => runPipeline(doc.fileName),
    );
  } catch (e) {
    vscode.window.showErrorMessage(`transpile.sh failed: ${(e as Error).message}`);
    return;
  }

  const map = readSourceMap(leanPath);
  if (!map || map.blocks.length === 0) {
    vscode.window.showInformationMessage('No @lean blocks found — nothing to verify.');
    diagCol.delete(doc.uri);
    richMessages.delete(doc.uri.toString());
    return;
  }

  // Open the .lean file so the Lean LSP server starts processing it.
  // We don't actually show it — opening the TextDocument is enough.
  const leanUri = vscode.Uri.file(leanPath);
  await vscode.workspace.openTextDocument(leanUri);

  const cfg = vscode.workspace.getConfiguration('ghcCoreLean');
  const quietMs = cfg.get<number>('leanDiagnosticQuietMs') ?? 2000;
  const totalMs = cfg.get<number>('leanDiagnosticTimeoutMs') ?? 60000;

  const leanDiags = await vscode.window.withProgress(
    {
      location: vscode.ProgressLocation.Notification,
      title: 'GHC Core → Lean: waiting for Lean LSP…',
    },
    () => waitForLeanDiagnostics(leanUri, quietMs, totalMs),
  );

  const hsDiags: vscode.Diagnostic[] = [];
  const rich = new Map<string, string>();

  for (const d of leanDiags) {
    const leanLine = d.range.start.line + 1; // VS Code 0-based → 1-based
    const block = map.blocks.find(
      (b) => leanLine >= b.lean[0] && leanLine <= b.lean[1],
    );
    if (!block) continue;

    // Diagnostic is anchored to the entire @lean block in the .hs file.
    const hsRange = new vscode.Range(
      Math.max(0, block.hs[0] - 1),
      0,
      Math.max(0, block.hs[1] - 1),
      Number.MAX_SAFE_INTEGER,
    );

    const tag = severityLabel(d.severity);
    const message = `${tag}${d.message}`;
    const diag = new vscode.Diagnostic(hsRange, message, d.severity);
    diag.source = 'lean';
    hsDiags.push(diag);

    const key = `${block.hs[0]}-${block.hs[1]}`;
    rich.set(key, (rich.get(key) ?? '') + message + '\n\n');
  }

  diagCol.set(doc.uri, hsDiags);
  richMessages.set(doc.uri.toString(), rich);

  channel.appendLine(`Posted ${hsDiags.length} diagnostic(s) onto ${path.basename(doc.fileName)}.`);
  if (hsDiags.length === 0) {
    vscode.window.showInformationMessage(
      'No Lean diagnostics matched any @lean block — make sure the Lean4 extension is installed and Blaster is configured.',
    );
  }
}

function severityLabel(sev: vscode.DiagnosticSeverity): string {
  switch (sev) {
    case vscode.DiagnosticSeverity.Error: return 'ERROR: ';
    case vscode.DiagnosticSeverity.Warning: return 'WARNING: ';
    case vscode.DiagnosticSeverity.Information: return '';
    case vscode.DiagnosticSeverity.Hint: return 'hint: ';
    default: return '';
  }
}

class AnnotationHoverProvider implements vscode.HoverProvider {
  provideHover(
    doc: vscode.TextDocument,
    pos: vscode.Position,
  ): vscode.ProviderResult<vscode.Hover> {
    const rich = richMessages.get(doc.uri.toString());
    if (!rich) return null;
    const diags = diagCol.get(doc.uri) ?? [];
    const hit = diags.find((d) => d.range.contains(pos));
    if (!hit) return null;

    const startLine = hit.range.start.line + 1;
    const endLine = hit.range.end.line + 1;
    const content = rich.get(`${startLine}-${endLine}`);
    if (!content) return null;

    const md = new vscode.MarkdownString();
    md.appendMarkdown('**Lean verification result**\n\n');
    md.appendCodeblock(content.trim(), 'lean');
    md.isTrusted = false;
    return new vscode.Hover(md, hit.range);
  }
}

function clearDiagnostics(): void {
  diagCol.clear();
  richMessages.clear();
  channel.appendLine('Cleared all GHC Core → Lean diagnostics.');
}

export function activate(ctx: vscode.ExtensionContext): void {
  ctx.subscriptions.push(diagCol, channel);
  ctx.subscriptions.push(
    vscode.commands.registerCommand('ghcCoreLean.verify', verify),
    vscode.commands.registerCommand('ghcCoreLean.clearDiagnostics', clearDiagnostics),
    vscode.languages.registerHoverProvider('haskell', new AnnotationHoverProvider()),
  );
}

export function deactivate(): void {
  // Nothing to do — disposables are tracked via ctx.subscriptions.
}
