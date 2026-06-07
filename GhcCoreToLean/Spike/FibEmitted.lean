import Lean
import Blaster

namespace Spike.FibEmitted

def fib (ds : Int) : Int :=
  (let ds_inner := ds
(match ds_inner with
| 0 => (1 : Int)
| 1 => (1 : Int)
| _ => (((· + ·)) ((fib) ((((· - ·)) (ds_inner)) ((1 : Int))))) ((fib) ((((· - ·)) (ds_inner)) ((2 : Int))))))
decreasing_by all_goals sorry

#blaster [ fib 0 = 1 ]

end Spike.FibEmitted
