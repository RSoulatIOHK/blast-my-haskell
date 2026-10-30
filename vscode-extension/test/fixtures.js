const { createHash } = require('node:crypto');
function report(source = '/tmp/Test.hs', status = 'proved', options = {}) {
  const axioms = { proved: [], smt_valid: ['Blaster.Tactic.blasterProven'],
    admitted: ['sorryAx'], assumed: ['Test.assumption'] }[status];
  const properties = axioms ? [{ hs: [1, 3], status, theorems: [{ name: 'Test.property',
    line: 10, axioms, status }] }] : [];
  const policy = { semantics: 'conservative', trustSmt: false, ...options };
  return { schemaVersion: 1, runId: 'test-run', source, ...policy, claim: 'lean-model',
    translationCertified: false, status, phase: ['error', 'refuted'].includes(status) ? 'lean' : 'complete',
    accepted: status === 'proved' || (status === 'smt_valid' && policy.trustSmt), elapsedSeconds: 0.1,
    modules: [{ module: 'Test', source, sha256: createHash('sha256').update('a\nb\nc\n').digest('hex'),
      status, properties, diagnostics: [], warnings: '', stderr: '',
      sourceMap: { haskellPath: source, blocks: status === 'no_properties' ? [] : [{ hs: [1, 3], lean: [10, 12] }] } }] };
}
module.exports = { report };
