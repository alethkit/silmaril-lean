module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond

open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open SeaOfNodes.Diamond (Projection)
open Fixture

private def run (graph : Graph Fixture.args) (guard : Bool) : Tuple (WireVal 3) (Threaded wordPorts) :=
  graph.lower.run (leafModel 3).toRVSDG (graph.encodeEntry guard input initial)

-- Run the numbered target graph directly on the source fixture.
example : run (diamond .onTrue) true = encodeResult 11 afterTrue := rfl
example : run (diamond .onTrue) false = encodeResult 33 afterFalse := rfl
example : run (diamond .onFalse) true = encodeResult 11 afterTrue := rfl
example : run (diamond .onFalse) false = encodeResult 33 afterFalse := rfl

-- In reverse Region order, the false arm is first and the true arm is second.
example : (run (diamond .onFalse) true).get (.tail .head) falseCell = 0 := rfl
example : (run (diamond .onFalse) false).get (.tail .head) trueCell = 0 := rfl

-- The suffix can also return the arm's saved word through the γ data port.
example :
    run { diamond .onFalse with suffix := .ret (.latest 0) (.arg .head) } true =
      encodeResult 7 afterTrue := rfl

end Silmaril.SSA.SeaOfNodes.Memory.Diamond
