const { test } = require('node:test');
const assert = require('node:assert/strict');
const { parseReport, presentation } = require('../out/protocol');
const { report } = require('./fixtures');
const parse = r => parseReport(JSON.stringify(r), r.accepted ? 0 : 1, r.source, r);

test('completed proofs, trusted SMT, and rejected SMT retain distinct presentation', () => {
  for (const status of ['proved', 'smt_valid', 'admitted', 'assumed', 'no_properties']) {
    for (const trustSmt of [false, true]) {
      const r = parse(report(undefined, status, { trustSmt }));
      assert.equal(presentation(status, r).tone === 'success', status === 'proved');
    }
  }
  assert.match(presentation('smt_valid', report()).label, /trust required/);
  assert.match(presentation('proved', report(undefined, 'proved', { semantics: 'approximate' })).label, /approximate/);
});
test('silence, log text, truncation, multiple documents, and unknown schema never pass', () => {
  const r = report();
  for (const output of ['', '✅ Valid', '{', JSON.stringify(r) + JSON.stringify(r),
    JSON.stringify({ ...r, schemaVersion: 2 })]) {
    assert.throws(() => parseReport(output, 0, r.source, r));
  }
});
test('exit, source, and policy must match the request', () => {
  const r = report();
  for (const code of [null, 1, 2]) assert.throws(() => parseReport(JSON.stringify(r), code, r.source, r));
  assert.throws(() => parseReport(JSON.stringify(r), 0, '/tmp/Different.hs', r));
  assert.throws(() => parseReport(JSON.stringify(r), 0, r.source, { ...r, trustSmt: true }));
  assert.throws(() => parseReport(JSON.stringify(r), 0, r.source, { ...r, semantics: 'approximate' }));
});
test('acceptance cannot hide admissions, missing proofs, failed imports, or compiler errors', () => {
  const mutations = [
    r => r.modules[0].properties[0].theorems[0].axioms.push('sorryAx'),
    r => r.modules[0].properties[0].theorems.splice(0),
    r => r.modules[0].properties.splice(0),
    r => r.modules.splice(0),
    r => r.modules[0].diagnostics.push({ severity: 'error', data: 'unknown identifier' }),
    r => r.modules.unshift({ ...r.modules[0], source: '/tmp/Dependency.hs', status: 'error',
      properties: [], sourceMap: { haskellPath: '/tmp/Dependency.hs', blocks: [] } }),
    r => r.modules[0].properties[0].hs = [0, 3],
    r => r.modules[0].properties[0].theorems[0].line = 20,
  ];
  for (const mutate of mutations) { const r = report(); mutate(r); assert.throws(() => parse(r)); }
});
test('negative completion and incomplete runs never become green', () => {
  for (const status of ['unsupported', 'timeout', 'cancelled', 'stale', 'error']) {
    const r = { ...report(), status, phase: 'transpile', accepted: false, modules: [] };
    assert.equal(parse(r).status, status);
    assert.notEqual(presentation(status, r).tone, 'success');
    assert.equal(presentation('proved', r).tone, 'warning');
  }
  assert.match(presentation('error', report()).label, /error/);
  assert.match(presentation('refuted', report()).label, /Refuted.*Lean model/);
});
