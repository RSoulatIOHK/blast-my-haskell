import GhcCoreToLean.Maps
import GhcCoreToLean.Emit
import GhcCoreToLean.AST

namespace GhcCoreToLean.Tests
open GHCCore GHCCore.Maps GHCCore.Emit

-- Sentinel: proves the harness builds and `#guard` failures break the build.
#guard valueMap "GHC.Base.id" == some "id"

end GhcCoreToLean.Tests
