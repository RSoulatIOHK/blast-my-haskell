// Exercise the registered commands/providers with the VS Code API boundary
// mocked. Files, hashes, run generations, and editor event ordering are real.
const { test, before, after, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
const os = require('node:os');
const Module = require('node:module');
const { report } = require('./fixtures');
const runner = require('../out/runner');
const { RunError } = runner;
const disposable = () => ({ dispose() {} });
class EventEmitter {
  listeners = new Set();
  event = fn => { this.listeners.add(fn); return { dispose: () => this.listeners.delete(fn) }; };
  fire = e => { for (const fn of [...this.listeners]) fn(e); };
  dispose() { this.listeners.clear(); }
}
class Range {
  constructor(a,b,c,d) { this.start={line:a,character:b}; this.end={line:c,character:d}; }
  contains(p) { return p.line >= this.start.line && p.line <= this.end.line; }
}
const file = fsPath => ({ scheme: 'file', fsPath, toString: () => 'file://' + fsPath });
class Diagnostic { constructor(range,message,severity){Object.assign(this,{range,message,severity});} }
class MarkdownString { appendCodeblock(text){this.value=text;return this;} }
class RelativePattern { constructor(base,pattern){Object.assign(this,{base,pattern});} }
const editEvent = new EventEmitter(), configEvent = new EventEmitter();
const commands = new Map(), posted = new Map(), watchers = [], calls = [], notifications = [], progressUpdates = [];
let hover, lenses, folder, source, doc, extension;
let policy = { semantics:'conservative', trustSmt:false };
let runImplementation;
const collection = { clear:()=>posted.clear(), set:(uri,ds)=>posted.set(uri.toString(),ds),
  get:uri=>posted.get(uri.toString()), dispose(){} };
const mock = {
  EventEmitter, Range, Diagnostic, MarkdownString, RelativePattern, Uri: { file },
  DiagnosticSeverity:{Error:0,Warning:1,Information:2}, ProgressLocation:{Notification:1}, OverviewRulerLane:{Right:4},
  Hover:class { constructor(contents,range){Object.assign(this,{contents,range});} },
  CodeLens:class { constructor(range,command){Object.assign(this,{range,command});} },
  commands:{registerCommand(name,fn){commands.set(name,fn);return disposable();}},
  languages:{createDiagnosticCollection:()=>collection,
    registerHoverProvider(_selector,provider){hover=provider;return disposable();},
    registerCodeLensProvider(_selector,provider){lenses=provider;return disposable();}},
  window:{visibleTextEditors:[],activeTextEditor:undefined,
    createOutputChannel:()=>({appendLine(){},show(){},dispose(){}}),
    createTextEditorDecorationType:options=>({...options,dispose(){}}),
    onDidChangeVisibleTextEditors:()=>disposable(),
    showWarningMessage:async message=>notifications.push(message),
    showInformationMessage:async message=>notifications.push(message),
    withProgress:async(_options,fn)=>fn({report:update=>progressUpdates.push(update)}, {isCancellationRequested:false,onCancellationRequested:()=>disposable()})},
  workspace:{isTrusted:true,textDocuments:[],workspaceFolders:[],
    getWorkspaceFolder:()=>({uri:file(folder)}),
    getConfiguration:()=>({get:(key,fallback)=>policy[key]??fallback}),
    openTextDocument:async uri=>{
      const known=mock.workspace.textDocuments.find(d=>d.uri.fsPath===uri.fsPath);
      if(known)return known;
      const loaded=makeDoc(uri.fsPath);mock.workspace.textDocuments.push(loaded);return loaded;
    },
    onDidChangeTextDocument:editEvent.event,onDidChangeConfiguration:configEvent.event,
    createFileSystemWatcher(){
      const change=new EventEmitter(),create=new EventEmitter(),del=new EventEmitter();
      const w={change,create,del,onDidChange:change.event,onDidCreate:create.event,onDidDelete:del.event,
        dispose(){change.dispose();create.dispose();del.dispose();}};
      watchers.push(w);return w;
    }},
};
function makeDoc(source){return {uri:file(source),fileName:source,isDirty:false,lineCount:4,
  lineAt:()=>({text:'line'}),save:async()=>true};}
function titles(){return lenses.provideCodeLenses(doc).map(l=>l.command.title);}
async function waitForCall(count){for(let i=0;i<100&&calls.length<count;i++)await new Promise(r=>setTimeout(r,2));assert.equal(calls.length,count);}
before(async()=>{
  folder=await fs.mkdtemp(path.join(os.tmpdir(),'editor verification '));source=path.join(folder,'Test.hs');
  await fs.writeFile(source,'a\nb\nc\n');
  const original=Module._load;
  Module._load=function(name,...args){return name==='vscode'?mock:original.call(this,name,...args);};
  try{extension=require('../out/extension');}finally{Module._load=original;}
  runner.runVerifier=async options=>{calls.push(options);return runImplementation(options);};
  extension.activate({subscriptions:[]});
});
beforeEach(()=>{
  commands.get('ghcCoreLean.clearDiagnostics')();calls.length=0;notifications.length=0;progressUpdates.length=0;
  policy={semantics:'conservative',trustSmt:false};
  doc=makeDoc(source);mock.workspace.textDocuments=[doc];
  mock.window.activeTextEditor={document:doc};
  runImplementation=async()=>report(source);
});
after(async()=>{extension.deactivate();await fs.rm(folder,{recursive:true,force:true});});
test('proof gets a gutter/CodeLens result and hover without requiring Lean LSP',async()=>{
  await commands.get('ghcCoreLean.verify')();
  assert.match(titles()[0],/^✓ Proved.*Lean model/);
  const h=hover.provideHover(doc,{line:1,character:0});
  assert.match(h.contents.value,/Axioms: none/);
  assert.match(h.contents.value,/not certified/);
  assert.equal(calls[0].semantics,'conservative');assert.equal(calls[0].trustSmt,false);
});
test('notification shows startup and live phases before a verdict exists',async()=>{
  let resolve;runImplementation=()=>new Promise(r=>resolve=r);
  const pending=commands.get('ghcCoreLean.verify')();await waitForCall(1);
  assert.match(progressUpdates[0].message,/Starting verifier.*elapsed/);
  calls[0].onProgress('Building Haskell with GHC (Cabal)');
  assert.match(progressUpdates.at(-1).message,/Building Haskell.*elapsed/);
  assert.deepEqual(titles(),[]);
  resolve(report(source));await pending;
});
test('canonical CLI paths still publish on the original editor URI',async()=>{
  runImplementation=async options=>report(options.source);
  await commands.get('ghcCoreLean.verify')();
  assert.match(titles()[0],/^✓ Proved/);
  assert.equal(mock.workspace.textDocuments.length,1);
});
test('SMT stays amber with or without trust; admissions stay rejected',async()=>{
  for(const status of ['smt_valid','admitted','assumed']){
    for(const trustSmt of [false,true]){
      policy.trustSmt=trustSmt;runImplementation=async()=>report(source,status,policy);
      await commands.get('ghcCoreLean.verify')();
      assert.match(titles()[0],/^⚠/);
      assert.ok(posted.get(doc.uri.toString()).some(d=>d.severity===1));
    }
  }
});
test('edit during verification aborts the run and discards a late successful report',async()=>{
  let resolve;runImplementation=()=>new Promise(r=>resolve=r);
  const pending=commands.get('ghcCoreLean.verify')();await waitForCall(1);
  doc.isDirty=true;editEvent.fire({document:doc,contentChanges:[{}]});
  assert.equal(calls[0].signal.aborted,true);
  resolve(report(source));await pending;
  assert.deepEqual(titles(),[]);assert.equal(posted.size,0);
});
test('a newer run wins even when the older run finishes last',async()=>{
  let first;runImplementation=()=>new Promise(r=>first=r);
  const pending=commands.get('ghcCoreLean.verify')();await waitForCall(1);
  runImplementation=async()=>report(source,'admitted');
  await commands.get('ghcCoreLean.verify')();
  first(report(source));await pending;
  assert.equal(calls[0].signal.aborted,true);assert.match(titles()[0],/Admitted/);
});
test('clear cancels pending work and prevents repopulation',async()=>{
  let resolve;runImplementation=()=>new Promise(r=>resolve=r);
  const pending=commands.get('ghcCoreLean.verify')();await waitForCall(1);
  commands.get('ghcCoreLean.clearDiagnostics')();resolve(report(source));await pending;
  assert.equal(posted.size,0);assert.deepEqual(titles(),[]);
});
test('buffer edits, disk changes, and trust changes clear already displayed results',async()=>{
  for(const change of [()=>editEvent.fire({document:doc,contentChanges:[{}]}),
    ()=>configEvent.fire({affectsConfiguration:()=>true})]){
    await commands.get('ghcCoreLean.verify')();assert.equal(titles().length,1);
    change();assert.deepEqual(titles(),[]);assert.equal(posted.size,0);
  }
});
test('delayed save notifications with identical bytes preserve results',async()=>{
  await commands.get('ghcCoreLean.verify')();
  watchers[0].change.fire(doc.uri);
  await new Promise(r=>setTimeout(r,20));
  assert.match(titles()[0],/^✓ Proved/);
});
test('changed bytes on disk invalidate results',async()=>{
  await commands.get('ghcCoreLean.verify')();
  await fs.writeFile(source,'changed\n');watchers[0].change.fire(doc.uri);
  for(let i=0;i<50&&titles().length;i++)await new Promise(r=>setTimeout(r,2));
  assert.deepEqual(titles(),[]);
  await fs.writeFile(source,'a\nb\nc\n');
});
test('unsaved imports prevent verification',async()=>{
  mock.workspace.textDocuments.push({...makeDoc(path.join(folder,'Dependency.hs')),isDirty:true});
  await commands.get('ghcCoreLean.verify')();assert.equal(calls.length,0);
  assert.match(notifications[0],/Save the other/);
});
test('post-process hash mismatch never displays a proof',async()=>{
  runImplementation=async()=>{const r=report(source);r.modules[0].sha256='0'.repeat(64);return r;};
  await commands.get('ghcCoreLean.verify')();assert.deepEqual(titles(),[]);
  assert.match(notifications[0],/changed/);
});
test('a failed run clears older proof markers and exposes its error',async()=>{
  await commands.get('ghcCoreLean.verify')();assert.equal(titles().length,1);
  runImplementation=async()=>{throw new RunError('error','Malformed protocol');};
  await commands.get('ghcCoreLean.verify')();assert.deepEqual(titles(),[]);
  assert.match(posted.get(doc.uri.toString())[0].message,/Malformed protocol/);
});
test('dependency errors outside annotation blocks remain visible on dependency and entry',async()=>{
  const dependency=path.join(folder,'Dependency.hs');await fs.writeFile(dependency,'a\nb\nc\n');
  runImplementation=async()=>{
    const r=report(dependency,'error');r.source=source;
    r.modules[0].diagnostics=[{severity:'error',data:'unknown identifier in generated code',pos:{line:1,column:0}}];
    return r;
  };
  await commands.get('ghcCoreLean.verify')();
  assert.ok(posted.get(file(dependency).toString()).some(d=>d.message.includes('unknown identifier')));
  assert.ok(posted.get(doc.uri.toString()).some(d=>d.message.includes('Verification error')));
  assert.deepEqual(titles(),[]);
});
