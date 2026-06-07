import GhcCoreToLean

open GHCCore

def emittedHeader : String :=
  "import Lean\nimport Blaster\n\n"

/-- GHC desugars every module with `$trModule` / `$tcFib` / etc. — runtime
    type-rep plumbing that has no Blaster-relevant meaning and references
    GHC.Types symbols we don't translate. Drop them at the boundary. -/
private def isGhcRuntimePlumbing (name : Name) : Bool :=
  name.startsWith "$tr" || name.startsWith "$tc"

private def filterBind : Bind → Bool
  | .nonRec v _ => !isGhcRuntimePlumbing v.name
  | .rec_ pairs => pairs.any (fun (v, _) => !isGhcRuntimePlumbing v.name)

/-- Collect the top-level binder names from a (filtered) CoreProgram, in the
    order they appear in the source. -/
private def topBinderNames (prog : CoreProgram) : List Name :=
  (prog.foldl (init := []) fun acc b => match b with
    | .nonRec v _ => v.name :: acc
    | .rec_ pairs => pairs.foldl (init := acc) fun acc (v, _) => v.name :: acc).reverse

/-- A one-line-per-binding crib showing the original Haskell name and the
    Lean-emitted name. Helps annotation authors know what to reference. -/
private def emitNamesCrib (prog : CoreProgram) : String :=
  let names := topBinderNames prog
  if names.isEmpty then ""
  else
    let lines := names.map fun n =>
      let lean := Emit.sanitize n
      if n == lean then s!"--   {n}"
      else s!"--   {n}  →  {lean}"
    "-- Top-level bindings transpiled from the source module\n"
      ++ "-- (Haskell name → Lean name; bare entries are unchanged):\n"
      ++ String.intercalate "\n" lines
      ++ "\n\n"

def runTranspile (input : System.FilePath) (output : System.FilePath) : IO UInt32 := do
  let src ← IO.FS.readFile input
  match parseCoreProgramFromString src with
  | .error msg =>
    IO.eprintln s!"parse error: {msg}"
    pure 1
  | .ok prog => do
    let userProg := prog.filter filterBind
    let lowered  := Lower.lowerProgram userProg
    let body     := Emit.emitProgram lowered
    let crib     := emitNamesCrib userProg
    IO.FS.writeFile output (emittedHeader ++ crib ++ body ++ "\n")
    IO.println s!"wrote {output}"
    pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => runTranspile input output
  | _ => do
    IO.eprintln "usage: ghccoretolean <in.json> <out.lean>"
    pure 1
