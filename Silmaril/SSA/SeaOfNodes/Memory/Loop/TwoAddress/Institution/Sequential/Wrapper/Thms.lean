module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper.Admission
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper.Observation

/-! Both emitted wrappers satisfy the existing single-runtime check and
observe the complete result of their respective canonical θ. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper

open RVSDG (Tuple)
open RVSDG.NestedTheta.ExplicitRuntime (EntryChecked)
open RVSDG.NestedTheta.Institution

variable {args : List ValueSort} {cells : Nat}

def producerChecked (graph : Graph args) :
    EntryChecked (a := inputData args) (b := inputData (.word :: args)) (producer graph).toTerm :=
  (RVSDG.NestedTheta.Term.toTerm_toGraph _).symm ▸ Admission.wrapChecked graph (fun p => p) (producerWires graph)

def consumerChecked (graph : Graph args) :
    EntryChecked (a := inputData (.word :: args)) (b := inputData [.word, .word]) (consumer graph).toTerm :=
  (RVSDG.NestedTheta.Term.toTerm_toGraph _).symm ▸ Admission.wrapChecked graph (fun p => .tail p) (consumerWires graph)

theorem producer_observe (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (producer graph) (encodeInput initial input) =
      (RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower graph)
        (encodeInput initial input)).map (producerOutput input) :=
  Proofs.producer_observe graph input initial

theorem consumer_observe (graph : Graph args) (first : Word) (input : Tuple (Val cells) args) (initial : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (consumer graph) (Boundary.packet first input initial) =
      (RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower graph)
        (encodeInput initial input)).map (consumerOutput first) :=
  Proofs.consumer_observe graph first input initial

private theorem map_absent_iff {A B : Type} (f : A → B) (value : Part A) :
    value.map f = Part.none ↔ value = Part.none :=
  Part.eq_none_iff'.trans (@Part.eq_none_iff' A value).symm

theorem producer_absent_iff (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (producer graph) (encodeInput initial input) = Part.none ↔
      RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower graph)
        (encodeInput initial input) = Part.none := by
  rw [producer_observe]
  exact map_absent_iff (producerOutput input) _

theorem consumer_absent_iff (graph : Graph args) (first : Word) (input : Tuple (Val cells) args) (initial : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (consumer graph)
        (Boundary.packet first input initial) = Part.none ↔
      RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower graph)
        (encodeInput initial input) = Part.none := by
  rw [consumer_observe]
  exact map_absent_iff (consumerOutput first) _

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper
