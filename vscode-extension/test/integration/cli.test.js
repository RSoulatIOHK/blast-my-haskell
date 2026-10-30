const { test } = require('node:test');
const assert = require('node:assert/strict');
const path = require('node:path');
const { runVerifier } = require('../../out/runner');
const { presentation } = require('../../out/protocol');
const repo = path.resolve(__dirname, '../../..');
const fixture = name => path.join(repo, 'tests/fixtures/verification', name + '.hs');
const options = name => ({ script: path.join(repo, 'verify.sh'), source: fixture(name), cwd: repo,
  semantics: 'conservative', trustSmt: false, timeoutSeconds: 180,
  signal: new AbortController().signal, log: () => {} });
for (const [name, status, trustSmt, accepted] of [
  ['PureInteger', 'proved', false, true], ['SmtInteger', 'smt_valid', false, false],
  ['SmtInteger', 'smt_valid', true, true], ['Admitted', 'admitted', false, false],
  ['Refuted', 'refuted', false, false], ['Overflow', 'proved', false, true],
]) {
  test(`real CLI: ${name}, trustSmt=${trustSmt} → ${status}`, { timeout: 190000 }, async () => {
    const r = await runVerifier({ ...options(name), trustSmt });
    assert.equal(r.status, status); assert.equal(r.accepted, accepted);
    assert.equal(presentation(r.status, r).tone === 'success', status === 'proved');
  });
}
test('real CLI whole-run timeout remains incomplete', { timeout: 10000 }, async () => {
  const r = await runVerifier({ ...options('PureInteger'), timeoutSeconds: 0.001 });
  assert.equal(r.status, 'timeout'); assert.equal(r.accepted, false);
});
test('real CLI cancellation exits without an accepted result', { timeout: 10000 }, async () => {
  const controller = new AbortController();
  const pending = runVerifier({ ...options('PureInteger'), signal: controller.signal });
  setTimeout(() => controller.abort(), 500);
  await assert.rejects(pending, e => e.status === 'cancelled');
});
