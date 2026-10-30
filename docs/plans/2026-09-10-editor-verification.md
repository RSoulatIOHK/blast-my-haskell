# Audited editor integration

Scope: connect VS Code to the completed verification protocol delivered in the
previous milestone, while retaining gutter icons, CodeLens, annotation hovers,
and environment diagnostics. Preserve the user's existing version bump and
error-over-success precedence.

1. Replace shared exported-file/LSP polling with `verify.sh --json` in private
   CLI builds. Validate schema, source/policy, exit code, and proof assumptions.
2. Present distinct proof/trust/failure statuses. Keep errors in imports and
   generated code visible. Make the model-only claim explicit.
3. Cancel and invalidate stale work on edits, newer runs, settings changes,
   and Clear. Recheck source hashes and reject dirty imported buffers.
4. Add protocol, subprocess, editor lifecycle, and real CLI integration tests;
   run them in CI and document setup and migration from old settings.

Implementation is in `vscode-extension/src/{extension,protocol,runner}.ts`.
No Lean semantics or CLI proof policy changes are part of this milestone.

Validation completed:

- 24 Node tests: protocol consistency, subprocess completion/cancellation,
  and mocked editor lifecycle, including canonical path aliases and delayed
  save notifications.
- Eight fresh GHC → Lean runs through the TypeScript runner: proved, SMT with
  and without trust, admitted, refuted, unsupported, timeout, and cancellation.
- Real VS Code 1.131.0 Extension Development Host, isolated profile without
  Lean4: three Haskell fixtures with proved/SMT/admitted CodeLens and axiom
  hovers; editing clears results. This exposed and led to fixes for macOS
  path aliases, shutdown disposal, and delayed filesystem notifications.
- All 56 existing saved CLI reports parsed under the new protocol validator.
- Devcontainer builds now explicitly include the audit/library target.
- Packaged the private development extension as `ghccoretolean-vscode-0.5.2.vsix`;
  tests, sources, dependencies, and editor launch settings are excluded.

Remaining work: narrower invalidation through dependency tracking, verification
caching, real Cabal component integration, and the dictionary-preserving
IR/research milestones. The minimum declared VS Code version and native
Windows have not been tested locally.
