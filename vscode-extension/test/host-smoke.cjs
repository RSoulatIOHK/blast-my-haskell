const vscode = require('vscode');
const assert = require('node:assert/strict');
const path = require('node:path');
const fs = require('node:fs/promises');
async function smoke() {
  const extension = vscode.extensions.getExtension('iohk-spike.ghccoretolean-vscode');
  assert.ok(extension, 'development extension loaded');
  await extension.activate();
  assert.equal(vscode.extensions.getExtension('leanprover.lean4'), undefined, 'smoke test has no Lean4 extension');
  const root = vscode.workspace.workspaceFolders[0].uri.fsPath;
  for (const [fixture, label] of [['PureInteger', /^✓ Proved.*Lean model/],
    ['SmtInteger', /^⚠ SMT valid.*trust required/], ['Admitted', /^⚠ Admitted/]]) {
    const uri = vscode.Uri.file(path.join(root, fixture + '.hs'));
    const doc = await vscode.workspace.openTextDocument(uri);
    assert.equal(doc.languageId, 'haskell', '.hs files activate without another Haskell extension');
    const editor = await vscode.window.showTextDocument(doc);
    await vscode.commands.executeCommand('ghcCoreLean.verify');
    const lenses = await vscode.commands.executeCommand('vscode.executeCodeLensProvider', uri);
    assert.ok(lenses.some(l => label.test(l.command?.title ?? '')), JSON.stringify({ fixture, lenses,
      diagnostics: vscode.languages.getDiagnostics(uri).map(d=>d.message) }));
    const hovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', uri, new vscode.Position(4, 0));
    assert.ok(hovers.some(h => h.contents.some(c => c.value?.includes('Axioms:'))), 'annotation hover contains audited assumptions');
    console.log(`HOST PASS ${fixture}: ${lenses.map(l=>l.command?.title).join('; ')}`);
    await editor.edit(edit => edit.insert(new vscode.Position(doc.lineCount, 0), '\n'));
    const after = await vscode.commands.executeCommand('vscode.executeCodeLensProvider', uri);
    assert.equal(after.length, 0, 'editing removes completed results');
    assert.equal(vscode.languages.getDiagnostics(uri).length, 0);
    // All changes are in the disposable scratch workspace.
    await doc.save();
  }
  console.log('HOST PASS completed results, proof assumptions, and edit invalidation without Lean LSP');
  await fs.writeFile(path.join(path.dirname(root), 'host-result.json'), JSON.stringify({
    passed: ['PureInteger', 'SmtInteger', 'Admitted'], vscodeVersion: vscode.version,
    leanExtensionInstalled: false, editInvalidation: true,
  }));
}
exports.run = async () => {
  try { await smoke(); }
  catch (error) {
    const root = vscode.workspace.workspaceFolders[0].uri.fsPath;
    await fs.writeFile(path.join(path.dirname(root), 'host-failure.txt'), String(error.stack ?? error));
    throw error;
  }
};
