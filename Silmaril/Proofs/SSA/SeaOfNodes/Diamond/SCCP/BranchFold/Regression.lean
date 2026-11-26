module

import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Example.Defs

open Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Example

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold

open Semantics.Dataflow (Flat)
open SCCP.Example (model nat)

-- Control disappears from the emitted graph and the two wires can select different producers.
example : originalRegions .onTrue = [0, 0, 0, 0, 2] := by decide
example : originalRegions .onFalse = [0, 0, 0, 0, 2] := by decide
example : report .onTrue (.constant ⟨true⟩) true 4 = some (some 1, [0, 0, 0], 8) := by decide
example : report .onFalse (.constant ⟨true⟩) true 4 = some (some 1, [0, 0, 0], 8) := by decide
example : report .onFalse (.constant ⟨true⟩) true 12 = some (some 1, [0, 0, 0], 24) := by decide
example : report .onTrue (.constant ⟨false⟩) false 4 = some (some 2, [0, 0, 0], 99) := by decide
example : report .onFalse (.constant ⟨false⟩) false 4 = some (some 2, [0, 0, 0], 99) := by decide

example :
    letI : DecidableEq (sortValue model.value nat) := inferInstanceAs (DecidableEq Nat)
    (SCCP.solve model (graph .onFalse) (entryFacts (.constant ⟨true⟩))).2.2 = (.overdefined : Flat Nat) := rfl

-- Either runtime guard is possible with overdefined evidence. Bottom gives no evidence.
example : report .onTrue .overdefined true 4 = none := by decide
example : report .onFalse .bottom false 4 = none := by decide

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold
