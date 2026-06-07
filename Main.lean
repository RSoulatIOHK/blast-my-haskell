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

def runTranspile (input : System.FilePath) (output : System.FilePath) : IO UInt32 := do
  let src ← IO.FS.readFile input
  match parseProgramFromString src with
  | .error msg =>
    IO.eprintln s!"parse error: {msg}"
    pure 1
  | .ok prog => do
    let userBinds := prog.binds.filterMap keepBinding
    let lowered   := Lower.lowerProgram userBinds
    let userProg  : Program := { prog with binds := lowered }
    let body      := Emit.emitFullProgram userProg
    let crib      := emitNamesCrib userProg
    IO.FS.writeFile output (emittedHeader ++ crib ++ body ++ "\n")
    IO.println s!"wrote {output}"
    pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => runTranspile input output
  | _ => do
    IO.eprintln "usage: ghccoretolean <in.json> <out.lean>"
    pure 1
