import Lean

open Lean Elab Command

/-- Report theorem dependencies from the current module, after elaboration.
    This reports evidence about the Lean model, not correctness of translation.
    Declaration positions let the driver associate theorems with source blocks.
    `collectAxioms` follows both statement and proof dependencies. -/
elab "#ghc_audit" : command => do
  let env ← getEnv
  let mut entries : Array Json := #[]
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name |>.isNone then
      if let .thmInfo _ := info then
        if let some ranges ← findDeclarationRanges? name then
          let axioms ← collectAxioms name
          entries := entries.push <| Json.mkObj [
            ("name", toJson name.toString),
            ("line", toJson ranges.range.pos.line),
            ("axioms", toJson (axioms.map Name.toString))]
  logInfo m!"GHCCORE_AUDIT:{(Json.arr entries).compress}"
