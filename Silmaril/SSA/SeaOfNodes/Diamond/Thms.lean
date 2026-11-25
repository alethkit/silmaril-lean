module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs
public import Silmaril.SSA.RVSDG.Categorical.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Correctness

/-! Correctness of the γ lowering for the finite acyclic pure diamond. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond

open RVSDG (Tuple)
open RVSDG.Categorical (pack)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}
variable (m : Model.{u, v, w} Op)

/-- Each projection enters the Region at its assigned slot. -/
theorem Merge.predecessor_slot (merge : Merge) (projection : Projection) :
    merge.predecessor (merge.slot projection) = projection :=
  Proofs.predecessor_slot merge projection

/-- Each Region slot selects exactly its own predecessor. -/
theorem Merge.slot_predecessor (merge : Merge) (slot : Slot) :
    merge.slot (merge.predecessor slot) = slot :=
  Proofs.slot_predecessor merge slot

/-- The finite return relation has exactly the result of the source denotation. -/
theorem Graph.returns_iff_denote (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out) :
    g.Returns m entry result ↔ g.denote m entry = result :=
  Proofs.returns_iff_denote g entry result

/-- Lowering preserves and reflects each finite return observation. -/
theorem Graph.lower_returns_iff (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out) :
    g.Returns m entry result ↔ g.lower.run m.toRVSDG entry = .cons result .nil :=
  Proofs.lower_returns_iff g entry result

/-- The RVSDG categorical fold in types agrees with the source denotation,
under the target's tuple representation. -/
theorem Graph.lower_denote (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) :
    g.lower.denote (RVSDG.Categorical.Model.ofRuntime m.toRVSDG) (pack entry) =
      pack (.cons (g.denote m entry) .nil) :=
  Proofs.lower_denote g entry

end Silmaril.SSA.SeaOfNodes.Diamond
