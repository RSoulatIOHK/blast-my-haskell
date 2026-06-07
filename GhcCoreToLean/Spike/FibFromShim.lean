import Lean
import Blaster

-- This file is the end-to-end spike result:
--   fib.hs ── ghc (-fplugin GhcDump.Plugin) ──▸ Fib.pass-0000.cbor
--          ── shim/ghc-core-shim ──▸ fib.json
--          ── ghccoretolean ──▸ /tmp/fib_out.lean
-- The body below is `cat /tmp/fib_out.lean` pasted under a namespace so the
-- top-level `def fib` does not collide with neighbouring spike files.

namespace Spike.FibFromShim

def fib (ds_3070 : Int) : Int :=
  (let ds_3071 := ds_3070
(match ds_3071 with
| 0 => (1 : Int)
| 1 => (1 : Int)
| _ => (((· + ·)) ((fib) ((((· - ·)) (ds_3070)) ((1 : Int))))) ((fib) ((((· - ·)) (ds_3070)) ((2 : Int))))))
decreasing_by all_goals sorry

#blaster [ fib 0 = 1 ]

end Spike.FibFromShim
