module

public import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Thms
import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Pass.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery

open Silmaril.SSA.SeaOfNodes
open Diamond (Ty Val ValueSort dataPorts)
open GVN (Producer)
open Silmaril.SSA.SeaOfNodes.Pure
open Pure.ConstantFold
open Pure.SubZero (model word)
open Pure.SuffixReplay
open Pure.SuffixReplay.Discovery
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {ports : List (Ty Unit)}
variable {block : Block inputs ports} {candidate : Producer block.flow word} {edit : Edit block}

theorem rightZero?_checked (accepted : rightZero? block candidate = some edit) :
    ∃ applied, AddIdealize.step ⟨fun _ => none⟩ block.program candidate = .ok (some applied) ∧
      applied.rule = .rightZero ∧ edit.rule = .rightZero ∧ edit.state = fromRewrite block applied.rewrite := by
  cases checked : AddIdealize.step ⟨fun _ => none⟩ block.program candidate with
  | error reason => simp [rightZero?, checked] at accepted
  | ok result =>
    cases result with
    | none => simp [rightZero?, checked] at accepted
    | some applied =>
      by_cases selected : applied.rule = .rightZero
      · by_cases shorter : applied.rewrite.sigs'.length + 1 = block.sigs.length
        · simp [rightZero?, checked, selected, shorter] at accepted
          subst edit
          exact ⟨_, rfl, selected, rfl, rfl⟩
        · simp [rightZero?, checked, selected, shorter] at accepted
      · simp [rightZero?, checked, selected] at accepted

private theorem unused_agrees (accepted : unused? block candidate = some edit)
    (entry : Tuple (Val model.value) (dataPorts inputs)) : Agrees block edit.state entry := by
  obtain ⟨deleted, checked, rfl⟩ := Option.map_eq_some_iff.mp accepted
  exact ⟨Deletion.delete?_agrees checked model entry PUnit.unit, (Deletion.delete?_eq_some_iff.mp checked).2⟩

theorem step?_checked (accepted : step? block = some edit) :
    ∃ candidate : Producer block.flow word,
      rightZero? block candidate = some edit ∨ unused? block candidate = some edit := by
  cases found : (RightIdentityPass.wordProducers block.flow).findSome? (rightZero? block) with
  | none =>
    have chosen : (RightIdentityPass.wordProducers block.flow).findSome? (unused? block) = some edit := by
      simpa [step?, found] using accepted
    obtain ⟨candidate, _, checked⟩ := List.exists_of_findSome?_eq_some chosen
    exact ⟨candidate, .inr checked⟩
  | some first =>
    have same : first = edit := by simpa [step?, found] using accepted
    subst edit
    obtain ⟨candidate, _, checked⟩ := List.exists_of_findSome?_eq_some found
    exact ⟨candidate, .inl checked⟩

theorem step_agrees (accepted : step? block = some edit) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Agrees block edit.state entry := by
  obtain ⟨candidate, checked | checked⟩ := step?_checked accepted
  · obtain ⟨applied, chosen, _, _, same⟩ := rightZero?_checked checked
    rw [same]
    exact fromRewrite_agrees applied.rewrite entry (AddIdealize.step_agrees chosen entry)
  · exact unused_agrees checked entry

private theorem mem_producers (candidate : Producer block.flow word) :
    candidate ∈ RightIdentityPass.wordProducers block.flow :=
  List.mem_filterMap.mpr ⟨⟨word, candidate⟩, GVN.Pass.mem_candidates candidate, rfl⟩

theorem step?_eq_none_iff (block : Block inputs ports) : step? block = none ↔ NoEligible block := by
  have scan_iff (check : Producer block.flow word → Option (Edit block)) :
      (RightIdentityPass.wordProducers block.flow).findSome? check = none ↔ ∀ candidate, check candidate = none :=
    ⟨fun miss candidate => List.findSome?_eq_none_iff.mp miss candidate (mem_producers candidate),
      fun miss => List.findSome?_eq_none_iff.mpr fun candidate _ => miss candidate⟩
  have noFirst : step? block = none ↔
      (RightIdentityPass.wordProducers block.flow).findSome? (rightZero? block) = none ∧
        (RightIdentityPass.wordProducers block.flow).findSome? (unused? block) = none := by
    cases first : (RightIdentityPass.wordProducers block.flow).findSome? (rightZero? block) <;> simp [step?, first]
  rw [noFirst, scan_iff, scan_iff]
  exact ⟨fun miss candidate => ⟨miss.1 candidate, miss.2 candidate⟩,
    fun miss => ⟨fun candidate => (miss candidate).1, fun candidate => (miss candidate).2⟩⟩

private theorem run_spec (fuel : Nat) (block : Block inputs ports) (enough : block.sigs.length < fuel) :
    let final := Discovery.run fuel block enough
    (final.state.block.sigs.length + final.rules.length = block.sigs.length ∧ NoEligible final.state.block) ∧
      ∀ entry : Tuple (Val model.value) (dataPorts inputs), Agrees block final.state entry := by
  induction fuel generalizing block with
  | zero => exact (Nat.not_lt_zero _ enough).elim
  | succ fuel ih =>
    dsimp only [Discovery.run]
    split
    · rename_i missing
      exact ⟨⟨by simp [initial], (step?_eq_none_iff block).mp missing⟩,
        fun entry => run_agrees (requests := []) rfl entry⟩
    · rename_i edit checked
      have size := edit.shorter
      obtain ⟨⟨tailSize, stopped⟩, tailAgrees⟩ := ih edit.state.block (by omega)
      refine ⟨⟨?_, stopped⟩, fun entry => compose_agrees entry (step_agrees checked entry) (tailAgrees entry)⟩
      simp only [State.compose, List.length_cons]
      omega

theorem normalize_spec (block : Block inputs ports) :
    let final := normalize block
    (final.state.block.sigs.length + final.rules.length = block.sigs.length ∧ NoEligible final.state.block) ∧
      ∀ entry : Tuple (Val model.value) (dataPorts inputs), Agrees block final.state entry :=
  run_spec _ block (Nat.lt_succ_self _)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery
