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
    IO.FS.writeFile output (emittedHeader ++ body ++ "\n")
    IO.println s!"wrote {output}"
    pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => runTranspile input output
  | _ => do
    IO.eprintln "usage: ghccoretolean <in.json> <out.lean>"
    pure 1
