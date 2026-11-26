module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Refinement.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.ObservationInclusion

/-! # A bind obstruction for literal finite observation inclusion -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Capture

open Silmaril.Elgot.ITree (Tree Visible Approx)

/-- A producer with one visible request suffices to refute continuation
monotonicity for literal inclusion at each finite observation depth. -/
theorem exists_exact_observation_bind_counterexample :
    ∃ (Event : Type → Type) (producer : Tree Event Unit) (left right : Unit → Tree Event Unit),
      (∀ (reply : Unit) (depth : Nat) (node : Visible Event Unit (Approx Event Unit depth)),
        node ∈ (left reply).observe (depth + 1) → node ∈ (right reply).observe (depth + 1)) ∧
      ∃ (depth : Nat) (node : Visible Event Unit (Approx Event Unit depth)),
        node ∈ (producer >>= left).observe (depth + 1) ∧
          node ∉ (producer >>= right).observe (depth + 1) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.exists_exact_observation_bind_counterexample

end Silmaril.Isotope.Bridge.NamedFlat.Capture
