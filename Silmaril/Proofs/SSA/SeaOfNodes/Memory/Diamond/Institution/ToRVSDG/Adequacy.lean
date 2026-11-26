module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG.Proofs

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open SeaOfNodes.Diamond (Merge Projection)

variable {P Q : Signature} {args : List ValueSort} {cells : Nat}

theorem translated_satisfaction (e : Equation P) (model : Model P) :
    (room P).Sat (Discrete.mk model) (translateEquation e) ↔ e.Holds model := by
  constructor
  · intro holds guard initial
    let result := model.observe e.lhs guard initial
    have source := (model.returns_iff_observe e.lhs guard initial result.1 result.2).2 rfl
    have observed := (e.lhs.lower_returns_iff guard model.input initial result.1 result.2).1 source
    have equal := holds guard initial
    have observed' : (Program.ofGraph e.rhs).observe model guard initial = encodeResult result.1 result.2 :=
      equal.symm.trans observed
    have source' := (e.rhs.lower_returns_iff guard model.input initial result.1 result.2).2 observed'
    exact ((model.returns_iff_observe e.rhs guard initial result.1 result.2).1 source').symm
  · intro holds guard initial
    exact (e.lhs.lower_run guard model.input initial).trans
      ((congrArg (fun result : Word × Heap model.cells => encodeResult result.1 result.2)
        (holds guard initial)).trans (e.rhs.lower_run guard model.input initial).symm)

theorem behavior_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : Model Q)
    (guard : Bool) (initial : Heap model.cells) :
    (Program.ofGraph (mapGraph h graph)).observe model guard initial =
      (Program.ofGraph graph).observe (reduct h model) guard initial :=
  ((mapGraph h graph).lower_run guard model.input initial).trans
    ((congrArg (fun result : Word × Heap model.cells => encodeResult result.1 result.2)
      (observe_mapGraph h model graph guard initial)).trans
      (graph.lower_run guard (reduct h model).input initial).symm)

private theorem encodeInput_surjective
    (entry : Tuple (WireVal cells) (Threaded (dataPorts args))) :
    ∃ (input : Tuple (Val cells) args) (heap : Heap cells), encodeInput heap input = entry := by
  induction args with
  | nil =>
    cases entry with
    | cons heap tail =>
      cases tail
      exact ⟨.nil, heap, rfl⟩
  | cons sort args ih =>
    cases entry with
    | cons scalar tail =>
      obtain ⟨input, heap, rfl⟩ := ih tail
      exact ⟨.cons scalar input, heap, rfl⟩

private theorem slotIndex_indexSlot (i : Fin 2) : slotIndex (indexSlot i) = i :=
  Fin.cases rfl (fun j => by rw [Fin.eq_zero j]; rfl) i

private theorem encodeEntry_surjective (merge : Merge)
    (entry : Tuple (WireVal cells) (Threaded (inputPorts args))) :
    ∃ (guard : Bool) (input : Tuple (Val cells) args) (heap : Heap cells),
      encodeEntry merge guard input heap = entry := by
  cases entry with
  | cons selector tail =>
    obtain ⟨input, heap, rfl⟩ := encodeInput_surjective tail
    rcases selector with ⟨i⟩
    have available : ∃ guard, Projection.ofBool guard = merge.predecessor (indexSlot i) := by
      cases merge.predecessor (indexSlot i) with
      | onTrue => exact ⟨true, rfl⟩
      | onFalse => exact ⟨false, rfl⟩
    obtain ⟨guard, selected⟩ := available
    refine ⟨guard, input, heap, ?_⟩
    simp only [encodeEntry, selected, merge.slot_predecessor, slotIndex_indexSlot]

theorem shared_input_satisfaction (e : CompiledEquation P)
    (aligned : e.lhs.merge = e.rhs.merge) (cells : Nat) :
    (RVSDG.Institution.room.{0, 0, 0} targetSignature).Sat
        (Discrete.mk (leafModel cells).toRVSDG) e.sharedInputEquation ↔
      ∀ input : Tuple (Val cells) P.args, (room P).Sat (Discrete.mk (⟨cells, input⟩ : Model P)) e := by
  constructor
  · intro universal input guard initial
    have equal := universal (encodeEntry e.lhs.merge guard input initial)
    simpa only [Program.observe, CompiledEquation.sharedInputEquation, ← aligned] using equal
  · intro family entry
    obtain ⟨guard, input, initial, rfl⟩ := encodeEntry_surjective e.lhs.merge entry
    have equal := family input guard initial
    simpa only [Program.observe, CompiledEquation.sharedInputEquation, ← aligned] using equal

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG.Proofs
