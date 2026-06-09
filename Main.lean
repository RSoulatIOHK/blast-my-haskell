import GhcCoreToLean

open GHCCore

def emittedHeader : String :=
  "import Lean\nimport Blaster\n\n"

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
  -- Auto-derived Show methods and instance dicts:
  name.startsWith "$fShow"  ||
  name.startsWith "$cshow"  ||
  name.startsWith "$sshow"

/-- The `$f<Class><Type>` bindings are instance dictionary literals — their
    rhs is the dict-constructor applied to the methods. We surface instances
    via the `instances` section of the JSON instead. -/
private def isInstanceDictBinding (name : Name) : Bool :=
  name.startsWith "$f"

/-- Default-method bindings GHC auto-derives. `$c/=` is `not ∘ (==)` — we
    don't need it (BEq supplies bne automatically) and emitting it creates a
    circular dependency on the BEq instance we're about to define. -/
private def isAutoDerivedDefault (name : Name) : Bool :=
  name == "$c/="

private def shouldDrop (n : Name) : Bool :=
  isGhcRuntimePlumbing n || isInstanceDictBinding n || isAutoDerivedDefault n

/-- Filter bindings, including splitting `Rec` groups: if a Rec lumps
    together a dict literal and a method, drop the dict half and keep the
    rest. Returns `none` when the whole bind should be dropped. -/
private def keepBinding (b : Bind) : Option Bind :=
  match b with
  | .nonRec v _ =>
    if shouldDrop v.name then none else some b
  | .rec_ pairs =>
    let kept := pairs.filter (fun (v, _) => !shouldDrop v.name)
    if kept.isEmpty then none else some (.rec_ kept)

/-- Top-level binder names from the (filtered) program. -/
private def topBinderNames (prog : CoreProgram) : List Name :=
  (prog.foldl (init := []) fun acc b => match b with
    | .nonRec v _ => v.name :: acc
    | .rec_ pairs => pairs.foldl (init := acc) fun acc (v, _) => v.name :: acc).reverse

private def emitNamesCrib (prog : Program) : String :=
  let names := topBinderNames prog.binds
  if names.isEmpty && prog.typeDecls.isEmpty && prog.instances.isEmpty then ""
  else
    let bindLines := names.map fun n =>
      let lean := Emit.sanitize n
      if n == lean then s!"--   {n}" else s!"--   {n}  →  {lean}"
    let typeLines := prog.typeDecls.map fun d =>
      s!"--   data {d.name}"
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

/-- Imported-type → defining-module map for cross-module references, read from
    the tab-separated file named by `EXT_TYPES_MANIFEST` (one `Type\tModule`
    per line). transpile.sh builds it from the dependencies' `.decls.json`. -/
def loadExtTypes : IO (List (String × String)) := do
  let some path ← IO.getEnv "EXT_TYPES_MANIFEST" | pure []
  if path.isEmpty || !(← System.FilePath.pathExists path) then pure [] else
  let s ← IO.FS.readFile path
  pure ((s.splitOn "\n").filterMap fun line =>
    match line.splitOn "\t" with
    | [t, m] => if t.isEmpty || m.isEmpty then none else some (t, m)
    | _      => none)

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
    let userBinds := prog.binds.filterMap keepBinding
    let lowered   := Lower.lowerProgram userBinds
    let userProg  : Program := { prog with binds := lowered }
    let extTypes  ← loadExtTypes
    let body      := Emit.emitFullProgram extTypes userProg
    let crib      := emitNamesCrib userProg
    -- Wrap the emitted defs in a `namespace <module>` so user bindings that
    -- shadow Lean builtins (e.g. an Int-typed `min`/`max`) resolve to the
    -- local def rather than colliding with `Min.min`/`Max.max`. The matching
    -- `end <module>` is appended by transpile.sh after the `@lean` blocks, so
    -- the theorems land inside the namespace too.
    let nsOpen := match moduleName with
      | some m => s!"namespace {m}\n\n"
      | none   => ""
    -- `import` lines for transpiled dependencies precede the namespace.
    let imports    ← loadLeanImports
    let depImports := String.join (imports.map (s!"import {·}\n"))
    let header     := s!"import Lean\nimport Blaster\n{depImports}\n"
    let pre := header ++ nsOpen ++ crib ++ body ++ "\n"
    let specs ← loadSpecs moduleName
    let mut out := pre
    let mut leanCursor := (pre.splitOn "\n").length
    let mut blocks : List (Nat × Nat × Nat × Nat) := []   -- hsS hsE leanS leanE
    for (hsStart, hsEnd, raw) in specs do
      let resolved := Emit.resolveSpecText userProg.typeDecls extTypes raw.trim
      let nLines   := (resolved.splitOn "\n").length
      let leanS    := leanCursor + 1
      let leanE    := leanS + nLines - 1
      out := out ++ "\n" ++ resolved ++ "\n"
      blocks := (hsStart, hsEnd, leanS, leanE) :: blocks
      leanCursor := leanCursor + 1 + nLines
    IO.FS.writeFile output out
    let blockJson := String.intercalate ",\n    " (blocks.reverse.map fun (hs, he, ls, le) =>
      s!"\{ \"hs\": [{hs}, {he}], \"lean\": [{ls}, {le}] }")
    let mapJson := s!"\{\n  \"haskellPath\": \"\",\n  \"leanPath\": \"{output}\",\n  \"blocks\": [\n    {blockJson}\n  ]\n}\n"
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
