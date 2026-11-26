module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Defs
public import Silmaril.Semantics.Dataflow.Flat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Proofs

open Semantics.Dataflow (Flat)
open RVSDG (Port Origin Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data} {value : Data → Type w}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op}

private theorem readPort_mono {ports : List (Ty Data)} {t : Ty Data} (p : Port ports t) :
    Monotone (readPort (value := value) p) := by
  induction p with
  | head => exact fun _ _ h => h 0
  | tail _ ih => exact fun _ _ h => ih fun i => h i.succ

private theorem readFact_mono (entry : Tuple (Fact value) args) {t : Ty Data} (wire : Origin args past t) :
    Monotone (fun facts => readFact entry facts wire) := by
  intro old new h
  cases wire with
  | arg _ => exact le_rfl
  | output node port => exact readPort_mono port (h node)

private theorem branchEdges_mono (merge : Merge) :
    Monotone (branchEdges.{w} merge) := by
  intro a b hab
  change Flat.le a b at hab
  cases a <;> cases b <;> simp_all [branchEdges, Flat.le]

private theorem gate_of_marked {α : Type*} {edges : Executable} {slot : Slot}
    (marked : Marked edges slot) (fact : Flat α) : gate edges slot fact = fact := by
  change slotIndex slot ∈ edges at marked
  simp [gate, marked]

private theorem gate_le_of_marked_le {α : Type*} {edges : Executable} (slot : Slot)
    {fact upper : Flat α} (h : Marked edges slot → fact ≤ upper) : gate edges slot fact ≤ upper := by
  by_cases marked : slotIndex slot ∈ edges
  · simpa [gate, marked] using h marked
  · simp [gate, marked]

theorem operand_le_phiFact [DecidableEq (sortValue value out)] (phi : Phi args past out)
    {edges : Executable} (entry : Tuple (Fact value) args) (facts : ProducerFacts value past)
    (slot : Slot) (marked : Marked edges slot) :
    readFact entry facts (phi.operand slot) ≤ phiFact phi edges entry facts := by
  have gated : gate edges slot (readFact entry facts (phi.operand slot)) ≤ phiFact phi edges entry facts := by
    cases slot with
    | first => exact Flat.le_join_left (α := sortValue value out) _ _
    | second => exact Flat.le_join_right (α := sortValue value out) _ _
  rwa [gate_of_marked marked] at gated

theorem phiFact_le_iff [DecidableEq (sortValue value out)] (phi : Phi args past out) (edges : Executable)
    (entry : Tuple (Fact value) args) (facts : ProducerFacts value past)
    (upper : Flat (sortValue value out)) :
    phiFact phi edges entry facts ≤ upper ↔
      ∀ slot, Marked edges slot → readFact entry facts (phi.operand slot) ≤ upper := by
  constructor
  · exact fun h slot marked => (operand_le_phiFact phi entry facts slot marked).trans h
  · exact fun h => Flat.join_le (gate_le_of_marked_le .first (h .first))
      (gate_le_of_marked_le .second (h .second))

theorem transfer_mono [DecidableEq (sortValue m.value out)] (g : Graph Op inputs sigs out)
    (entry : Tuple (Fact m.value) (dataPorts inputs)) : Monotone (transfer m g entry) := by
  intro a b hab
  refine ⟨branchEdges_mono _ (readFact_mono _ _ hab.2.1), le_rfl, ?_⟩
  apply (phiFact_le_iff _ _ _ _ _).mpr
  intro slot marked
  exact (readFact_mono _ _ hab.2.1).trans
    ((phiFact_le_iff _ _ _ _ _).mp le_rfl slot (hab.1 marked))

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Proofs
