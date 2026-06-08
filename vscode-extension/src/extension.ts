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

// Wavy underline like Lean's info/warning squiggle, but recolored. Green for
// ✅ Valid, red for ❌ Falsified. No background fill — just the underline,
// matching the look of a regular diagnostic squiggle. The overview-ruler
// marker keeps the outcome visible when the line is offscreen.
const successDecoration = vscode.window.createTextEditorDecorationType({
  textDecoration: 'underline wavy rgb(46, 204, 113)',
  overviewRulerColor: 'rgba(46, 204, 113, 0.7)',
  overviewRulerLane: vscode.OverviewRulerLane.Right,
});

const failureDecoration = vscode.window.createTextEditorDecorationType({
  textDecoration: 'underline wavy rgb(231, 76, 60)',
  overviewRulerColor: 'rgba(231, 76, 60, 0.7)',
  overviewRulerLane: vscode.OverviewRulerLane.Right,
});

interface BlockDecorations {
  success: vscode.DecorationOptions[];
  failure: vscode.DecorationOptions[];
}

// Per-.hs-URI decoration state, so we can re-apply when the user switches
// back to the editor (decorations are editor-scoped, not document-scoped).
const decorationsByUri = new Map<string, BlockDecorations>();

function classify(msg: string): 'success' | 'failure' | 'other' {
  if (msg.includes('✅ Valid')) return 'success';
  if (msg.includes('❌ Falsified') || msg.toLowerCase().includes('falsified')) return 'failure';
  return 'other';
}

function applyDecorations(uri: vscode.Uri): void {
  const state = decorationsByUri.get(uri.toString());
  for (const editor of vscode.window.visibleTextEditors) {
    if (editor.document.uri.toString() !== uri.toString()) continue;
    editor.setDecorations(successDecoration, state?.success ?? []);
    editor.setDecorations(failureDecoration, state?.failure ?? []);
  }
}

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
      // transpile.sh prints "wrote <path>.lean" for the entry module, last,
      // after any dependency modules it also transpiled. Take the final match
      // so we resolve the entry's output, not a dependency's.
      const re = /wrote (\S+\.lean)/g;
      let m: RegExpExecArray | null;
      let last: string | undefined;
      while ((m = re.exec(stdout)) !== null) last = m[1];
      if (last) resolve(last);
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
  // Per-block outcome aggregation. A block flips to 'failure' as soon as any
  // diagnostic inside it is classified as failure; otherwise, if at least one
  // success-classified diagnostic landed in it, the block is 'success'.
  type Outcome = { kind: 'success' | 'failure'; block: Block };
  const blockOutcomes = new Map<string, Outcome>();

  for (const d of leanDiags) {
    const leanLine = d.range.start.line + 1; // VS Code 0-based → 1-based
    const block = map.blocks.find(
      (b) => leanLine >= b.lean[0] && leanLine <= b.lean[1],
    );
    if (!block) continue;

    const klass = classify(d.message);
    const tag = severityLabel(d.severity);
    const message = `${tag}${d.message}`;
    const key = `${block.hs[0]}-${block.hs[1]}`;
    rich.set(key, (rich.get(key) ?? '') + message + '\n\n');

    if (klass === 'success') {
      if (!blockOutcomes.has(key)) {
        blockOutcomes.set(key, { kind: 'success', block });
      }
    } else if (klass === 'failure') {
      blockOutcomes.set(key, { kind: 'failure', block });
    }

    // Non-Blaster diagnostics still flow to the Problems pane on the block's
    // content range so the user can jump to them. Skip ✅ Valid since the
    // green squiggle is the only signal we want for success.
    if (klass !== 'success') {
      // Map the specific Lean line back to the .hs line for the diagnostic
      // anchor (Problems-pane jumping should land precisely, even though
      // the squiggle covers the whole declaration).
      const offsetInBlock = leanLine - block.lean[0];
      const hsLine = block.hs[0] + 1 + offsetInBlock;
      const lineIdx = Math.max(0, hsLine - 1);
      const range = new vscode.Range(lineIdx, 0, lineIdx, Number.MAX_SAFE_INTEGER);

      const sev = klass === 'failure' ? vscode.DiagnosticSeverity.Error : d.severity;
      const diag = new vscode.Diagnostic(range, message, sev);
      diag.source = 'lean';
      hsDiags.push(diag);
    }
  }

  // Build decoration options per block — span the *entire* `{- @lean ... -}`
  // comment block including the opener and closer lines, so the squiggle
  // covers everything the user can see as one annotation.
  const successRanges: vscode.DecorationOptions[] = [];
  const failureRanges: vscode.DecorationOptions[] = [];
  for (const [key, outcome] of blockOutcomes) {
    // block.hs is 1-based; VS Code Range is 0-based.
    const startLine = Math.max(0, outcome.block.hs[0] - 1);
    const endLine   = Math.max(startLine, outcome.block.hs[1] - 1);
    const range = new vscode.Range(startLine, 0, endLine, Number.MAX_SAFE_INTEGER);
    const hover = new vscode.MarkdownString();
    hover.appendCodeblock((rich.get(key) ?? '').trim(), 'lean');
    const opt: vscode.DecorationOptions = { range, hoverMessage: hover };
    if (outcome.kind === 'success') successRanges.push(opt);
    else failureRanges.push(opt);
  }

  diagCol.set(doc.uri, hsDiags);
  richMessages.set(doc.uri.toString(), rich);
  decorationsByUri.set(doc.uri.toString(), { success: successRanges, failure: failureRanges });
  applyDecorations(doc.uri);

  channel.appendLine(
    `Posted ${hsDiags.length} diagnostic(s) and ${successRanges.length}/${failureRanges.length} success/failure squiggles onto ${path.basename(doc.fileName)}.`,
  );
  if (hsDiags.length === 0 && successRanges.length === 0 && failureRanges.length === 0) {
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
  // Clear all editor decorations too.
  for (const [uriStr] of decorationsByUri) {
    const uri = vscode.Uri.parse(uriStr);
    for (const editor of vscode.window.visibleTextEditors) {
      if (editor.document.uri.toString() === uriStr) {
        editor.setDecorations(successDecoration, []);
        editor.setDecorations(failureDecoration, []);
      }
    }
    decorationsByUri.delete(uriStr);
    void uri;
  }
  channel.appendLine('Cleared all GHC Core → Lean diagnostics and decorations.');
}

export function activate(ctx: vscode.ExtensionContext): void {
  ctx.subscriptions.push(diagCol, channel, successDecoration, failureDecoration);
  ctx.subscriptions.push(
    vscode.commands.registerCommand('ghcCoreLean.verify', verify),
    vscode.commands.registerCommand('ghcCoreLean.clearDiagnostics', clearDiagnostics),
    vscode.languages.registerHoverProvider('haskell', new AnnotationHoverProvider()),
    // Decorations are editor-scoped, not document-scoped. Re-apply when the
    // user switches back to a .hs editor that has cached decorations.
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      if (editor) applyDecorations(editor.document.uri);
    }),
    vscode.window.onDidChangeVisibleTextEditors((editors) => {
      for (const e of editors) applyDecorations(e.document.uri);
    }),
  );
}

export function deactivate(): void {
  // Nothing to do — disposables are tracked via ctx.subscriptions.
}
