module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Dataflow.Thms
public import Silmaril.Semantics.Dataflow.Flat.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.Equations

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Proofs

open Semantics.Dataflow (Flat)
open RVSDG (Port Tuple Origin extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {args ports : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op}

private theorem readPort_tupleFacts {t : Ty Data} (p : Port ports t)
    (xs : Tuple (Fact m.value) ports) : readPort p (tupleFacts xs) = xs.get p := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs with | cons _ tail => exact ih tail

theorem fixed_read_covers [DecidableEq (sortValue m.value out)] (g : Graph Op inputs sigs out)
    {entryFacts : Tuple (Fact m.value) (dataPorts inputs)} {entry : Tuple (Val m.value) (dataPorts inputs)}
    (hentry : TupleCovers entryFacts entry) {state : State m.value sigs out}
    (fixed : transfer m g entryFacts state = state)
    {t : Ty Data} (wire : Origin (dataPorts inputs) (extend [] sigs) t) :
    (readFact entryFacts state.2.1 wire).Covers (read m wire entry (g.dataflow.eval m entry PUnit.unit)) := by
  have producers : producerFacts m g entryFacts = state.2.1 := congrArg (fun x => x.2.1) fixed
  rw [← producers]
  cases wire with
  | arg p => exact hentry p
  | output i p =>
    change (readPort p (tupleFacts ((evalFacts m entryFacts g.dataflow PUnit.unit).get i))).Covers _
    rw [readPort_tupleFacts]
    exact evalFacts_cover g.dataflow hentry (fun j => j.elim0) i p

private theorem branchEdges_covers (merge : Merge) {fact : Flat (ULift.{w} Bool)} {b : ULift.{w} Bool}
    (cover : fact.Covers b) :
    Marked (branchEdges merge fact) (merge.slot (Projection.ofBool b.down)) := by
  cases fact with
  | bottom => exact False.elim cover
  | constant b' =>
    change b' = b at cover
    subst b'
    exact Finset.mem_singleton_self _
  | overdefined => exact Finset.mem_univ _

theorem fixed_sound [DecidableEq (sortValue m.value out)] (g : Graph Op inputs sigs out)
    {entryFacts : Tuple (Fact m.value) (dataPorts inputs)} {entry : Tuple (Val m.value) (dataPorts inputs)}
    (hentry : TupleCovers entryFacts entry) {state : State m.value sigs out}
    (fixed : transfer m g entryFacts state = state) :
    Marked state.1 (takenSlot m g entry) ∧ state.2.2.Covers (g.denote m entry) := by
  have edges : branchEdges g.phi.merge (readFact entryFacts state.2.1 g.predicate) = state.1 :=
    congrArg Prod.fst fixed
  have marked : Marked state.1 (takenSlot m g entry) := by
    rw [← edges]
    exact branchEdges_covers g.phi.merge (fixed_read_covers g hentry fixed g.predicate)
  refine ⟨marked, ?_⟩
  have result : phiFact g.phi state.1 entryFacts state.2.1 = state.2.2 :=
    congrArg (fun x => x.2.2) fixed
  have cover := fixed_read_covers g hentry fixed (g.phi.operand (takenSlot m g entry))
  rw [← result]
  exact Flat.covers_mono (operand_le_phiFact g.phi entryFacts state.2.1 (takenSlot m g entry) marked) cover

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Proofs
