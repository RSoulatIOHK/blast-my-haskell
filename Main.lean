import GhcCoreToLean

open GHCCore

/-- GHC-generated runtime plumbing that has no Blaster-relevant meaning and
    references GHC.Types/GHC.Show internals we don't translate. -/
private def isGhcRuntimePlumbing (name : Name) : Bool :=
  name.startsWith "$tr"     ||  -- runtime type rep (Module/TrName)
  name.startsWith "$tc"     ||  -- TyCon type rep
  name.startsWith "$krep"   ||  -- kind rep helpers
  -- HasCallStack dict GHC float-lifts to top level for `error`; once the
  -- `error` collapses to `sorry` (Emit) the dict is dead and only references
  -- call-stack primitives with no Lean image, so drop it. (Lower already
  -- erases the same dict when it stays a local let.)
  name.startsWith "$dIP"    ||
  -- Auto-derived Show methods and instance dicts. The `$c` half is matched by
  -- EXACT name (`Emit.isDerivedShowMethod` — `Show`'s three methods) rather than
  -- by the prefix `$cshow`, which also ate a user class's `showIt`/`showAll`; see
  -- that docstring for the residual. The other two stay prefixes and are not
  -- method binds at all: `$fShow…` is a dict-builder (`$f` + the class name
  -- `Show` + the type), `$sshow…` a specialization of `show` itself.
  name.startsWith "$fShow"  ||
  Emit.isDerivedShowMethod name ||
  name.startsWith "$sshow"

/-- NOTE: `$f<Class><Type>` instance dict-builders are NOT dropped here — they
    reach `emitFullProgram`, which reads their bodies to reconstruct user-class
    declarations and then suppresses them from emission (they have no Lean
    image). `$fShow*` is still dropped above via `isGhcRuntimePlumbing`.

    The second rule is `Emit.isEqNeqBind`: GHC's auto-derived `/=` for an `Eq`
    instance (Lean's `BEq`/`DecidableEq` supplies `bne`, and the body would not
    elaborate anyway — see that docstring). It is deliberately keyed on the `Eq`
    instance HEADS, not on the name `$c/=` alone: the name-only test also ate the
    `/=` of a USER class declaring that operator, which then lost the whole
    instance. Bind-level (a `Var`, not a `Name`) because the head type comes from
    the bind's own type. -/
private def shouldDrop (insts : List Instance) (v : Var) : Bool :=
  isGhcRuntimePlumbing v.name || Emit.isEqNeqBind insts v

/-- Filter bindings, including splitting `Rec` groups: if a Rec lumps
    together a dict literal and a method, drop the dict half and keep the
    rest. Returns `none` when the whole bind should be dropped. -/
private def keepBinding (insts : List Instance) (b : Bind) : Option Bind :=
  match b with
  | .nonRec v _ =>
    if shouldDrop insts v then none else some b
  | .rec_ pairs =>
    let kept := pairs.filter (fun (v, _) => !shouldDrop insts v)
    if kept.isEmpty then none else some (.rec_ kept)

/-- Top-level binder names from the (filtered) program. -/
private def topBinderNames (prog : CoreProgram) : List Name :=
  (prog.foldl (init := []) fun acc b => match b with
    | .nonRec v _ => v.name :: acc
    | .rec_ pairs => pairs.foldl (init := acc) fun acc (v, _) => v.name :: acc).reverse

private def emitNamesCrib (extTypes : List (String × String))
    (extNts : List (Name × String)) (prog : Program) : String :=
  -- `$f` dict-builders survive into emitFullProgram (for class reconstruction)
  -- but are suppressed from emission; keep them out of the crib too.
  let names := (topBinderNames prog.binds).filter (fun n => !n.startsWith "$f")
  if names.isEmpty && prog.typeDecls.isEmpty && prog.instances.isEmpty then ""
  else
    let bindLines := names.map fun n =>
      let lean := Emit.sanitize n
      if n == lean then s!"--   {n}" else s!"--   {n}  →  {lean}"
    -- Dependency order, matching the order `emitFullProgram` emits the decls in
    -- (`sortDataDecls`) rather than the dump order. Newtypes appear here even
    -- though they emit no decl — the crib is the record of what the module
    -- declared, and the annotation is where a reader learns the type is gone.
    -- The underlying string is run through the same passes the emitted types are,
    -- in pipeline order: an IMPORTED newtype in the underlying (`newtype W = W Age`)
    -- erases at pass 2 from `extNts`, and an imported DATA type only becomes
    -- `RecordOps.Point` at pass 4. `newtypeSubsts` has already chained the LOCAL
    -- newtypes, so `extNts` is the only substitution missing. Without both, the crib
    -- comment would be the one place a raw needle still appears in generated output.
    let nts := (Emit.newtypeSubsts prog.typeDecls).map fun (n, u) =>
      (n, Emit.resolveExternalTypes extTypes (Emit.resolveNewtypes extNts u))
    let typeLines := (Emit.sortDataDecls prog.typeDecls).map fun d =>
      match nts.find? (·.1 == d.name) with
      | some (_, u) => s!"--   newtype {d.name} (erased → {u})"
      | none        => s!"--   data {d.name}"
    let instLines := prog.instances.filterMap fun i =>
      if i.className == "Eq" then
        let head := i.headTypes.map (Emit.emitType) |> String.intercalate " "
        some s!"--   instance {i.className} {head}"
      else none
    let all := typeLines ++ instLines ++ bindLines
    "-- Top-level symbols transpiled from the source module\n"
      ++ "-- (Haskell name → Lean name; bare entries are unchanged):\n"
      ++ String.intercalate "\n" all
      ++ "\n\n"

/-- Cross-module type information, read from the tab-separated file named by
    `EXT_TYPES_MANIFEST`. Two channels — `Type\tModule` (imported data type →
    defining module) and `Type\tnewtype\tUnderlying` (imported newtype → the type
    it erases to); see `Emit.parseExtManifest` and the manifest section header in
    `Emit.lean` for the format, and `transpile.sh` for who writes each channel.

    A line matching neither channel is WARNED about and skipped rather than fatal:
    the consequence of a dropped entry is a surviving `(GHCCore.tyConOpaque "T")`
    needle, i.e. a loud `lake build` failure, so skipping cannot be silent-wrong. -/
def loadExtManifest : IO Emit.ExtManifest := do
  let some path ← IO.getEnv "EXT_TYPES_MANIFEST" | pure {}
  if path.isEmpty || !(← System.FilePath.pathExists path) then pure {} else
  let m := Emit.parseExtManifest (← IO.FS.readFile path)
  for line in m.rejected do
    IO.eprintln s!"warning: EXT_TYPES_MANIFEST line matches no channel, skipped: {line}"
  for n in m.ambiguous do
    IO.eprintln s!"warning: two graph modules declare a DIFFERENT type named `{n}` — \
either a data type in one and a newtype in the other, or a newtype over two different \
underlying types; ALL its manifest entries are DROPPED (choosing a winner would erase \
`{n}` to the wrong type, which would typecheck and be silently wrong). References to \
`{n}` from this module will fail loud at `lake build`; rename one of the types."
  pure m

/-- Publish THIS module's erasable newtypes (`Emit.newtypeExports`) as manifest
    lines to the file named by `NEWTYPE_EXPORTS_OUT`; `transpile.sh` appends it to
    the shared manifest so the modules that IMPORT this one erase the newtype the
    same way this one does.

    Always truncates when the variable is set — including to EMPTY — because the
    sidecar lives in the sandbox's `.decls` directory, which persists across runs:
    a newtype deleted from the source must not leave a live entry behind. -/
def writeNewtypeExports (typeDecls : List DataDecl) : IO Unit := do
  let some path ← IO.getEnv "NEWTYPE_EXPORTS_OUT" | pure ()
  if path.isEmpty then pure () else
  let lines := (Emit.newtypeExports typeDecls).map fun (n, u) => Emit.newtypeManifestLine n u
  IO.FS.writeFile path (String.join (lines.map (· ++ "\n")))

/-- Lean modules to `import` for transpiled dependencies, from the
    space-separated `LEAN_IMPORTS` env var (e.g. `GhcCoreToLean.Generated.Ratio`). -/
def loadLeanImports : IO (List String) := do
  let some v ← IO.getEnv "LEAN_IMPORTS" | pure []
  pure ((v.splitOn " ").filter (!·.isEmpty))

/-- Read recorded specs for `moduleName` from
    `$LEAN_SPEC_DIR/<module>/<start>-<end>.lean`, sorted by start line. Each
    entry is `(hsStartLine, hsEndLine, leanText)`. -/
def loadSpecs (moduleName : Option String) : IO (List (Nat × Nat × String)) := do
  let some m := moduleName | pure []
  let some dir ← IO.getEnv "LEAN_SPEC_DIR" | pure []
  let modDir := System.FilePath.join dir m
  if !(← modDir.pathExists) then pure [] else
  let entries ← modDir.readDir
  let mut specs : List (Nat × Nat × String) := []
  for e in entries do
    let stem := e.fileName.dropRight 5            -- strip ".lean"
    match stem.splitOn "-" with
    | [s, en] =>
      match s.toNat?, en.toNat? with
      | some sl, some el => specs := (sl, el, ← IO.FS.readFile e.path) :: specs
      | _, _             => pure ()
    | _ => pure ()
  pure (specs.toArray.qsort (fun a b => a.1 < b.1)).toList

def runTranspile (input : System.FilePath) (output : System.FilePath)
    (moduleName : Option String) : IO UInt32 := do
  let src ← IO.FS.readFile input
  match parseProgramFromString src with
  | .error msg =>
    IO.eprintln s!"parse error: {msg}"
    pure 1
  | .ok prog => do
    -- The cross-module manifest is loaded FIRST because its `newtype` channel is
    -- an input to the validation below, not just to emission: an instance on an
    -- IMPORTED newtype is exactly as unrepresentable as one on a local newtype,
    -- and since that newtype's needle IS erased now (pass 2), letting it through
    -- would be silent-wrong rather than a loud `lake build` failure.
    let ext    ← loadExtManifest
    let extNts := ext.newtypes
    -- Program-level validation, BEFORE any emission (nothing is written below
    -- until the very end, so an early `return` leaves no partial output).
    -- Warn about malformed newtype dumps: they fall back to being emitted as
    -- data, which fails loud at `lake build` — this names the cause up front.
    for n in Emit.malformedNewtypes prog.typeDecls do
      IO.eprintln s!"warning: {Emit.malformedNewtypeWarning n}"
    -- Refuse a local type name that ALSO names a type reachable through the
    -- module graph. The Core dump spells imported type references BARE, so the
    -- two are indistinguishable and every resolution order is a blind guess —
    -- see Emit's "Local-vs-imported type-name collisions" section for the
    -- end-to-end probe. FIRST of the two program-level refusals: under a
    -- collision the newtype-instance message below would consult a substitution
    -- list that is itself ambiguous, and could name the wrong underlying type.
    --
    -- The DATA channel carries a self-entry for every graph module, this one
    -- included (`scripts/transpile_graph.py manifest` dumps all of them), so
    -- entries defined by THIS module are dropped first — they are not imports.
    -- With no module name we cannot tell a self-entry from an import, so the
    -- data channel is skipped entirely rather than refusing every module that
    -- declares a `data` type; the newtype channel needs no such filter (a
    -- module's own newtype lines are appended only AFTER it emits).
    let importedDataNames := match moduleName with
      | some m => (ext.datas.filter (·.2 != m)).map (·.1)
      | none   => []
    -- `ext.ambiguous` is in the set too: those entries were DROPPED, which makes
    -- an imported reference loud at `lake build` — but only while nothing else
    -- resolves the needle, and a local decl of the same name does exactly that.
    let importedNames := importedDataNames ++ ext.newtypes.map (·.1) ++ ext.ambiguous
    let collisions := Emit.localImportCollisions prog.typeDecls importedNames
    if !collisions.isEmpty then
      for c in collisions do
        IO.eprintln s!"error: {Emit.localImportCollisionError c}"
      return 1
    -- Refuse any instance whose head type is a newtype — local or imported:
    -- erasure has nowhere to put it and both fallbacks are silent-wrong. See
    -- Emit's "Newtype-instance guard" section for the observed shapes and for the
    -- invariant that ties this name set to the set pass 2 erases.
    let ntViolations :=
      Emit.newtypeInstanceViolations prog.instances prog.typeDecls (extNts.map (·.1))
    if !ntViolations.isEmpty then
      for v in ntViolations do
        IO.eprintln s!"error: {Emit.newtypeInstanceError prog.typeDecls v extNts}"
      return 1
    -- Publish this module's own erasable newtypes for its dependents. After the
    -- guard: a refused module aborts the whole pipeline (`transpile.sh` runs under
    -- `set -e`), so no dependent can read the file this run either way.
    writeNewtypeExports prog.typeDecls
    let userBinds := prog.binds.filterMap (keepBinding prog.instances)
    let lowered   := Lower.lowerProgram userBinds
    let userProg  : Program := { prog with binds := lowered }
    -- Refuse a method name declared by two classes: Core references a class
    -- method by its BARE name, so every call site would be qualified with
    -- whichever class the instance dump listed first — typechecks, dispatches to
    -- the wrong class. See Emit's "Same-named methods across classes" section for
    -- what is reachable (not the single-module shape: GHC rejects that itself).
    --
    -- Computed on `userProg` — post-filter, post-`Lower` — so the class set
    -- checked here is exactly the one `emitFullProgram` merges below. Still
    -- before any emission: nothing is written until the very end.
    let ambiguities := Emit.sameMethodAmbiguities userProg
    if !ambiguities.isEmpty then
      for (m, cs) in ambiguities do
        IO.eprintln s!"error: {Emit.sameMethodAmbiguityError m cs}"
      return 1
    -- Refuse a declared class method that would fall through to `Maps.valueMap`'s
    -- builtin of the same name (an operator method with no surviving `$c` bind).
    -- `emitVar`'s precedence puts `methodMap` first, which settles the case where
    -- the map HAS the entry; this settles the case where it does not. AFTER the
    -- ambiguity check: under an ambiguity the map's entries are unreliable, so
    -- reporting "no entry" first would name the wrong cause.
    let unmapped := Emit.unmappedOperatorMethods userProg
    if !unmapped.isEmpty then
      for (c, m) in unmapped do
        IO.eprintln s!"error: {Emit.unmappedOperatorMethodError c m}"
      return 1
    -- Name every instance `emitInstanceUser` is about to SKIP, and the method
    -- that costs it. Not a refusal (the skip is already loud at `lake build`, as
    -- `failed to synthesize`, and refusing would newly reject modules whose
    -- unusable instance is unused) — but no longer silent at the transpiler,
    -- which was the last silent half of that path. Same decision procedure the
    -- emission uses (`Emit.classifyInstanceMethod`), so the two cannot disagree.
    for (cls, head, m) in Emit.unresolvedInstanceMethods userProg do
      IO.eprintln s!"warning: {Emit.unresolvedInstanceMethodWarning cls head m}"
    -- Name every SUPERCLASS the emitted `class` block drops (M3 Task 5): one that
    -- is neither a locally-declared class (→ `extends`) nor a builtin with a
    -- `Maps.classConMap` recipe (→ constraint-site binders). Warning, not refusal,
    -- for the same reason as the instance skip above: a dropped parent whose
    -- methods are never called through the child costs nothing, and one whose
    -- methods ARE called is already loud at `lake build`. Without this the drop
    -- would be entirely silent at the transpiler — which is what the plugin's
    -- `ppSuperPred` comment had assumed Task 5 would prevent by other means.
    for (cls, super) in Emit.droppedSupers userProg do
      IO.eprintln s!"warning: {Emit.unmappedSuperWarning cls super}"
    -- Tripwire for the shim's role heuristic. A `$dm<method>` Var is a
    -- default-method BODY; the shim used to classify it as a dictionary (any
    -- `$d`-prefixed name), and `Lower` erases dict-role Vars in ARGUMENT
    -- position and at lambda/`let` binders — so a regression here would silently
    -- delete a default-method occurrence rather than fail. `$dm` is unambiguous
    -- (a dict is `$d` + a CLASS name, always upper-case), which is why the shim
    -- exempts it in both places it writes that rule (`binderRole` and
    -- `convertExternalName`); this says so out loud if a dump produced by some
    -- other/older shim arrives. The scan covers references, not just binders:
    -- the two shim copies can disagree, and one of them did.
    --
    -- Runs on `prog.binds` — the RAW dump, not `userProg` — and must: `Lower` has
    -- already deleted a dict-role occurrence in argument position, so a scan of
    -- the lowered program would find nothing to report about the very case that
    -- matters.
    for n in Emit.dmVarsMislabelledAsDicts prog.binds do
      IO.eprintln s!"warning: {Emit.dmDictRoleWarning n}"
    let body      := Emit.emitFullProgram ext.datas userProg extNts
    let crib      := emitNamesCrib ext.datas extNts userProg
    -- Wrap the emitted defs in a `namespace <module>` so user bindings that
    -- shadow Lean builtins (e.g. an Int-typed `min`/`max`) resolve to the
    -- local def rather than colliding with `Min.min`/`Max.max`. The matching
    -- `end <module>` is appended by transpile.sh; the specs are emitted by the
    -- transpiler below, inside this namespace.
    let nsOpen := match moduleName with
      | some m => s!"namespace {m}\n\n"
      | none   => ""
    -- `import` lines for transpiled dependencies precede the namespace.
    let imports    ← loadLeanImports
    let depImports := String.join (imports.map (s!"import {·}\n"))
    let header     := s!"import Lean\nimport Blaster\nimport GhcCoreToLean.Runtime\n{depImports}\n"
    let pre := header ++ nsOpen ++ crib ++ body ++ "\n"
    let specs ← loadSpecs moduleName
    let mut out := pre
    let mut leanCursor := (pre.splitOn "\n").length
    let mut blocks : List (Nat × Nat × Nat × Nat) := []   -- hsS hsE leanS leanE
    for (hsStart, hsEnd, raw) in specs do
      let resolved := Emit.resolveSpecText userProg.typeDecls ext.datas raw.trim extNts
      let nLines   := (resolved.splitOn "\n").length
      let leanS    := leanCursor + 1
      let leanE    := leanS + nLines - 1
      out := out ++ "\n" ++ resolved ++ "\n"
      blocks := (hsStart, hsEnd, leanS, leanE) :: blocks
      leanCursor := leanCursor + 1 + nLines
    IO.FS.writeFile output out
    let blockJson := String.intercalate ",\n    " (blocks.reverse.map fun (hs, he, ls, le) =>
      s!"\{ \"hs\": [{hs}, {he}], \"lean\": [{ls}, {le}] }")
    let escPath := (output.toString.replace "\\" "\\\\").replace "\"" "\\\""
    let mapJson := s!"\{\n  \"haskellPath\": \"\",\n  \"leanPath\": \"{escPath}\",\n  \"blocks\": [\n    {blockJson}\n  ]\n}\n"
    IO.FS.writeFile (output.toString ++ ".map.json") mapJson
    IO.println s!"wrote {output}"
    pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output]          => runTranspile input output none
  | [input, output, modname] => runTranspile input output (some modname)
  | _ => do
    IO.eprintln "usage: ghccoretolean <in.json> <out.lean> [moduleName]"
    pure 1
