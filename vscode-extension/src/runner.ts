import { spawn } from 'child_process';
import { Policy, Report, parseReport } from './protocol';

export class RunError extends Error {
  constructor(public readonly status: 'error' | 'timeout' | 'cancelled' | 'stale', message: string) { super(message); }
}
export interface RunOptions extends Policy {
  script: string; source: string; cwd: string; timeoutSeconds: number; signal: AbortSignal;
  log: (message: string) => void;
  onProgress?: (message: string) => void;
}

export function runVerifier(options: RunOptions): Promise<Report> {
  const { signal, timeoutSeconds } = options;
  if (!Number.isFinite(timeoutSeconds) || timeoutSeconds <= 0 || timeoutSeconds > 86400) {
    return Promise.reject(new RunError('error', 'Verification timeout must be between 0 and 86400 seconds.'));
  }
  if (signal.aborted) return Promise.reject(new RunError('cancelled', 'Verification cancelled.'));
  const args = [options.script, options.source, '--json', '--semantics', options.semantics,
    '--timeout', String(timeoutSeconds)];
  if (options.trustSmt) args.push('--trust-smt');
  return new Promise((resolve, reject) => {
    // verify.sh execs Python; SIGTERM lets Python clean up its separate GHC/Lean
    // process groups. Argument arrays preserve spaces and never invoke a shell command string.
    const grouped = process.platform !== 'win32';
    const proc = spawn('bash', args, { cwd: options.cwd, detached: grouped,
      env: { ...process.env, GHCCORE_PROGRESS: '1' }, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '', stderr = '', bytes = 0;
    let progressBuffer = '';
    let stopped: RunError | undefined;
    let escalation: NodeJS.Timeout | undefined;
    const kill = (signal: NodeJS.Signals) => {
      try {
        if (grouped && proc.pid !== undefined) process.kill(-proc.pid, signal);
        else proc.kill(signal);
      } catch (error) { if ((error as NodeJS.ErrnoException).code !== 'ESRCH') options.log(String(error)); }
    };
    const stop = (reason: RunError) => {
      if (stopped) return;
      stopped = reason;
      kill('SIGTERM');
      escalation = setTimeout(() => {
        kill('SIGKILL');
        // A broken custom wrapper must not keep this promise alive through
        // inherited pipes after the cancellation grace period.
        proc.stdout.destroy(); proc.stderr.destroy();
      }, 5000);
    };
    const abort = () => stop(new RunError('cancelled', 'Verification cancelled.'));
    signal.addEventListener('abort', abort, { once: true });
    // The CLI owns the actual deadline. This watchdog also bounds a broken wrapper.
    const timer = setTimeout(() => stop(new RunError('timeout', 'Verifier exceeded its time limit.')),
      timeoutSeconds * 1000 + 5000);
    const cleanup = () => {
      clearTimeout(timer); clearTimeout(escalation);
      signal.removeEventListener('abort', abort);
    };
    const collect = (stream: 'stdout' | 'stderr', chunk: string) => {
      bytes += Buffer.byteLength(chunk);
      if (bytes > 32 * 1024 * 1024) {
        stop(new RunError('error', 'Verifier output exceeded 32 MiB.'));
        return;
      }
      if (stream === 'stdout') stdout += chunk;
      else {
        stderr += chunk;
        progressBuffer += chunk;
        let newline: number;
        while ((newline = progressBuffer.indexOf('\n')) >= 0) {
          const line = progressBuffer.slice(0, newline);
          progressBuffer = progressBuffer.slice(newline + 1);
          if (!stopped && line.startsWith('GHCCORE_PROGRESS:')) {
            try {
              const event = JSON.parse(line.slice('GHCCORE_PROGRESS:'.length));
              if (typeof event.message === 'string' && event.message.length <= 300) options.onProgress?.(event.message);
            } catch { /* Progress is informational; it never determines a verdict. */ }
          }
        }
      }
    };
    proc.stdout.setEncoding('utf8').on('data', (chunk: string) => collect('stdout', chunk));
    proc.stderr.setEncoding('utf8').on('data', (chunk: string) => collect('stderr', chunk));
    proc.once('error', error => { cleanup(); reject(new RunError('error', error.message)); });
    // `close`, unlike `exit`, guarantees all output has been consumed.
    proc.once('close', (code, exitSignal) => {
      cleanup();
      options.log(`Verifier ${options.source}: exit ${code ?? exitSignal}${stopped ? '; result discarded: ' + stopped.status : ''}\n${stdout}${stderr ? '\nstderr:\n' + stderr : ''}`);
      if (stopped) { reject(stopped); return; }
      try { resolve(parseReport(stdout, code, options.source, options)); }
      catch (error) { reject(new RunError('error', `Verifier protocol failure: ${(error as Error).message}. See output for details.`)); }
    });
    if (signal.aborted) abort();
  });
}

/** Superseded, edited, cleared, or cancelled runs cannot publish late results. */
export class RunGate {
  private generation = 0;
  private controller?: AbortController;
  get version(): number { return this.generation; }
  invalidate(): void { this.generation++; this.controller?.abort(); this.controller = undefined; }
  begin(): { generation: number; signal: AbortSignal } {
    this.invalidate();
    this.controller = new AbortController();
    return { generation: this.generation, signal: this.controller.signal };
  }
  current(generation: number): boolean { return generation === this.generation; }
  finish(generation: number): void { if (this.current(generation)) this.controller = undefined; }
}
