const { test } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const os = require('node:os');
const path = require('node:path');
const { runVerifier, RunGate } = require('../out/runner');
const { report } = require('./fixtures');
const quote = s => "'" + s.replaceAll("'", "'\\''") + "'";
async function fixture(t, body, r = report()) {
  const cwd = await fs.mkdtemp(path.join(os.tmpdir(), 'verifier runner '));
  t.after(() => fs.rm(cwd, { recursive: true, force: true }));
  const script = path.join(cwd, 'verify script.sh');
  await fs.writeFile(script, body);
  return { script, cwd, source: r.source, semantics: r.semantics, trustSmt: r.trustSmt,
    timeoutSeconds: 5, signal: new AbortController().signal, log: () => {} };
}
test('runner consumes complete output and handles spaces and shell characters as arguments', async t => {
  const r = report('/tmp/a b $(false) \' quote.hs');
  const text = JSON.stringify(r), midpoint = Math.floor(text.length / 2);
  const options = await fixture(t, `test "$1" = ${quote(r.source)} || exit 7\nprintf '%s' ${quote(text.slice(0, midpoint))}\nsleep 0.02\nprintf '%s' ${quote(text.slice(midpoint))}`, r);
  assert.equal((await runVerifier(options)).status, 'proved');
});
test('exit 1 is a structured negative result, not a lost error report', async t => {
  const r = report(undefined, 'admitted');
  const options = await fixture(t, `printf '%s' ${quote(JSON.stringify(r))}\nexit 1`, r);
  assert.equal((await runVerifier(options)).status, 'admitted');
});
test('successful process with no result is a protocol error', async t => {
  const options = await fixture(t, 'echo "✅ Valid"');
  await assert.rejects(runVerifier(options), e => e.status === 'error');
});
test('cancellation waits for process exit and never accepts its output', async t => {
  const options = await fixture(t, 'exec sleep 30');
  const controller = new AbortController();
  const promise = runVerifier({ ...options, signal: controller.signal });
  setTimeout(() => controller.abort(), 30);
  await assert.rejects(promise, e => e.status === 'cancelled');
});
test('invalid deadlines and already cancelled work never start a process', async t => {
  const options = await fixture(t, 'exit 9');
  for (const timeoutSeconds of [0, -1, NaN, Infinity, 86401]) {
    await assert.rejects(runVerifier({ ...options, timeoutSeconds }), e => e.status === 'error');
  }
  await assert.rejects(runVerifier({ ...options, signal: AbortSignal.abort() }), e => e.status === 'cancelled');
});
test('generation gate discards late completion after edit, clear, and supersession', () => {
  const gate = new RunGate();
  const first = gate.begin();
  const second = gate.begin();
  assert.equal(first.signal.aborted, true);
  assert.equal(gate.current(first.generation), false);
  gate.finish(first.generation);
  assert.equal(second.signal.aborted, false);
  gate.invalidate();
  assert.equal(second.signal.aborted, true);
  assert.equal(gate.current(second.generation), false);
});
test('phase updates arrive before completion, including split stderr chunks', async t => {
  const r = report();
  const options = await fixture(t, `printf '%s' 'GHCCORE_PRO' >&2\nsleep 0.02\nprintf '%s\\n' 'GRESS:{"phase":"ghc","message":"Building Haskell"}' >&2\nsleep 0.02\nprintf '%s' ${quote(JSON.stringify(r))}`);
  let finished = false;
  const updates = [];
  const result = await runVerifier({ ...options, onProgress: message => {
    assert.equal(finished, false); updates.push(message);
  } });
  finished = true;
  assert.deepEqual(updates, ['Building Haskell']);
  assert.equal(result.status, 'proved');
});
test('progress claiming success is never a verification result', async t => {
  const options = await fixture(t, `printf '%s\\n' 'GHCCORE_PROGRESS:{"message":"Valid"}' >&2`);
  await assert.rejects(runVerifier(options), e => e.status === 'error');
});
