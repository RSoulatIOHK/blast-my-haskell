import * as path from 'path';

export type Status = 'proved' | 'smt_valid' | 'admitted' | 'assumed' | 'refuted' |
  'no_theorem' | 'no_properties' | 'unsupported' | 'error' | 'timeout' | 'cancelled' | 'stale';
export interface Policy { semantics: 'conservative' | 'approximate'; trustSmt: boolean }
export interface Block { hs: [number, number]; lean: [number, number] }
export interface Theorem { name: string; line: number; axioms: string[]; status: Status }
export interface Property { hs: [number, number]; status: Status; theorems: Theorem[] }
export interface LeanDiagnostic { severity: string; data: string; pos?: { line: number; column: number } }
export interface ModuleResult {
  module: string; source: string; sha256: string; status: Status;
  properties: Property[]; diagnostics: LeanDiagnostic[]; warnings: string; stderr: string;
  detail?: string;
  sourceMap: { haskellPath: string; blocks: Block[] };
}
export interface Report extends Policy {
  schemaVersion: 1; runId: string; source: string; claim: 'lean-model';
  translationCertified: false; status: Status; phase: string; accepted: boolean;
  elapsedSeconds: number; detail?: string; modules: ModuleResult[];
}

const statuses: Status[] = ['proved', 'smt_valid', 'admitted', 'assumed', 'refuted',
  'no_theorem', 'no_properties', 'unsupported', 'error', 'timeout', 'cancelled', 'stale'];
const standard = new Set(['propext', 'Classical.choice', 'Quot.sound']);
function check(condition: unknown): asserts condition {
  if (!condition) throw new Error('Invalid or inconsistent verifier JSON. Rebuild/update the CLI and extension together.');
}
function object(value: unknown): asserts value is Record<string, any> {
  check(value !== null && typeof value === 'object' && !Array.isArray(value));
}
function status(value: unknown): asserts value is Status { check(statuses.includes(value as Status)); }
function range(value: unknown): asserts value is [number, number] {
  check(Array.isArray(value) && value.length === 2 && value.every(Number.isSafeInteger) &&
    value[0] >= 1 && value[1] >= value[0]);
}
export function proofStatus(axioms: string[]): Status {
  const extra = axioms.filter(a => !standard.has(a));
  if (extra.includes('sorryAx')) return 'admitted';
  if (extra.some(a => a !== 'Blaster.Tactic.blasterProven')) return 'assumed';
  return extra.length ? 'smt_valid' : 'proved';
}
function aggregate(values: Status[], empty: Status): Status {
  if (!values.length) return empty;
  for (const s of ['error', 'refuted', 'admitted', 'assumed', 'no_theorem', 'smt_valid'] as Status[]) {
    if (values.includes(s)) return s;
  }
  return 'proved';
}
export function accepts(s: Status, policy: Policy): boolean {
  return s === 'proved' || (s === 'smt_valid' && policy.trustSmt);
}

/** A single completed CLI document is the only result protocol. No log scraping. */
export function parseReport(stdout: string, exitCode: number | null, source: string, policy: Policy): Report {
  const r: unknown = JSON.parse(stdout);
  object(r);
  check(r.schemaVersion === 1 && typeof r.runId === 'string' && r.runId.length > 0);
  check(typeof r.source === 'string' && path.resolve(r.source) === path.resolve(source));
  check(r.claim === 'lean-model' && r.translationCertified === false);
  check(r.semantics === policy.semantics && r.trustSmt === policy.trustSmt);
  status(r.status);
  check(typeof r.accepted === 'boolean' && r.accepted === accepts(r.status, policy));
  check(exitCode === (r.accepted ? 0 : 1));
  check(typeof r.phase === 'string' && Number.isFinite(r.elapsedSeconds) && r.elapsedSeconds >= 0);
  check(r.detail === undefined || typeof r.detail === 'string');
  check(Array.isArray(r.modules));
  const sources = new Set<string>();
  for (const m of r.modules) {
    object(m); status(m.status);
    check(typeof m.module === 'string' && typeof m.source === 'string' && path.isAbsolute(m.source));
    check(!sources.has(m.source)); sources.add(m.source);
    check(typeof m.sha256 === 'string' && /^[a-f0-9]{64}$/.test(m.sha256));
    check(typeof m.warnings === 'string' && typeof m.stderr === 'string');
    check(m.detail === undefined || typeof m.detail === 'string');
    object(m.sourceMap);
    check(m.sourceMap.haskellPath === m.source && Array.isArray(m.sourceMap.blocks));
    for (const b of m.sourceMap.blocks) { object(b); range(b.hs); range(b.lean); }
    check(Array.isArray(m.diagnostics));
    for (const d of m.diagnostics) {
      object(d); check(typeof d.severity === 'string' && typeof d.data === 'string');
      if (d.pos !== undefined) {
        object(d.pos); check(Number.isSafeInteger(d.pos.line) && d.pos.line >= 1 &&
          Number.isSafeInteger(d.pos.column) && d.pos.column >= 0);
      }
    }
    check(Array.isArray(m.properties));
    for (const p of m.properties) {
      object(p); range(p.hs); status(p.status); check(Array.isArray(p.theorems));
      const b = m.sourceMap.blocks.find((b: Block) => b.hs[0] === p.hs[0] && b.hs[1] === p.hs[1]);
      check(b);
      for (const t of p.theorems) {
        object(t);
        check(typeof t.name === 'string' && Number.isSafeInteger(t.line) && t.line >= b.lean[0] && t.line <= b.lean[1]);
        check(Array.isArray(t.axioms) && t.axioms.every((a: unknown) => typeof a === 'string'));
        check(t.status === proofStatus(t.axioms));
      }
      check(p.status === aggregate(p.theorems.map((t: Theorem) => t.status), 'no_theorem'));
    }
    if (!['error', 'refuted'].includes(m.status)) {
      check(m.properties.length === m.sourceMap.blocks.length);
      check(new Set(m.properties.map((p: Property) => p.hs.join(':'))).size === m.properties.length);
      check(m.status === aggregate(m.properties.map((p: Property) => p.status), 'no_properties'));
      check(!m.diagnostics.some((d: LeanDiagnostic) => d.severity === 'error'));
    }
  }
  if (r.phase === 'complete' || r.accepted) {
    check(r.phase === 'complete' && r.modules.length > 0);
    const entry = r.modules[r.modules.length - 1];
    check(entry.source === r.source);
    const expected = entry.status === 'no_properties' ? 'no_properties' :
      aggregate(r.modules.map((m: ModuleResult) => m.status).filter((s: Status) => s !== 'no_properties'), 'no_properties');
    check(r.status === expected);
  }
  return r as unknown as Report;
}

export type Tone = 'success' | 'warning' | 'failure';
export function presentation(s: Status, report: Pick<Report, 'semantics' | 'trustSmt' | 'accepted'>): { label: string; tone: Tone } {
  const model = `Lean model (${report.semantics})`;
  switch (s) {
    case 'proved': return { label: `Proved · ${model}${report.accepted ? '' : ' · run not accepted'}`,
      tone: report.accepted ? 'success' : 'warning' };
    case 'smt_valid': return { label: `SMT valid · ${model} · ${report.trustSmt ? 'SMT trusted' : 'SMT trust required'}`,
      tone: 'warning' };
    case 'refuted': return { label: `Refuted · ${model}`, tone: 'failure' };
    case 'error': return { label: 'Verification error', tone: 'failure' };
    case 'admitted': return { label: 'Admitted · depends on sorry', tone: 'warning' };
    case 'assumed': return { label: 'Assumed · additional axioms', tone: 'warning' };
    case 'no_theorem': return { label: 'No named theorem in annotation', tone: 'warning' };
    case 'no_properties': return { label: 'No properties to verify', tone: 'warning' };
    case 'unsupported': return { label: 'Unsupported by selected policy or translator', tone: 'warning' };
    case 'timeout': return { label: 'Verification timed out', tone: 'warning' };
    case 'cancelled': return { label: 'Verification cancelled', tone: 'warning' };
    case 'stale': return { label: 'Source changed · verify again', tone: 'warning' };
  }
}
