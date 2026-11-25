module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Network.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.CounterSemiringNetwork

/-! # Partition and reindex finite feedback elimination -/

public section

universe u v w u' v' w'

namespace Silmaril.Calco2019.CounterSemiring

variable {A : Type u} {B : Type v} {U : Type w}
  {A' : Type u'} {B' : Type v'} {V : Type w'}

/-- Eliminating a partitioned state set is staged elimination. -/
theorem eliminateStates_union [DecidableEq U] (s t : Finset U) (disjoint : Disjoint s t)
    (f : Network A B U) :
    eliminateStates (s ∪ t) f = eliminateStates s (eliminateStates t f) :=
  congrArg (fun m : Function.End (Network A B U) => m f)
    (Finset.noncommProd_union_of_disjoint disjoint (eliminateState (A := A) (B := B)) _)

/-- Restricting the input, output and feedback indices commutes with
eliminating the same selected feedback states. -/
theorem eliminateStates_reindex (s : Finset V) (e : V ↪ U)
    (row : A' ⊕ V → A ⊕ U) (col : B' ⊕ V → B ⊕ U)
    (hr : ∀ v, row (.inr v) = .inr (e v)) (hc : ∀ v, col (.inr v) = .inr (e v))
    (f : Network A B U) :
    eliminateStates s (fun x y => f (row x) (col y)) =
      fun x y => eliminateStates (s.map e) f (row x) (col y) :=
  Proofs.CounterSemiring.eliminate_reindex s e row col hr hc f

/-- If there are no edges between the selected states, each contribution
passes through just one selected state. -/
theorem eliminateStates_noInternalEdges (s : Finset U) (f : Network A B U)
    (noEdges : ∀ u ∈ s, ∀ v ∈ s, f (.inr u) (.inr v) = 0)
    (x : A ⊕ U) (y : B ⊕ U) :
    eliminateStates s f x y = f x y + ∑ u ∈ s, f x (.inr u) * f (.inr u) y :=
  Proofs.CounterSemiring.eliminate_acyclic s f noEdges x y

end Silmaril.Calco2019.CounterSemiring
