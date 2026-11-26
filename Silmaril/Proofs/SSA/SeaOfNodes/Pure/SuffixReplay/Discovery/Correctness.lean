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

private theorem checkedEdit_fields {rule : Rule} {state : State inputs ports block.sigs}
    (accepted : checkedEdit? block rule state = some edit) : edit.rule = rule ∧ edit.state = state := by
  by_cases valid : state.block.sigs.length + (if rule.erases then 1 else 0) = block.sigs.length ∧
      weight state.block < weight block
  · simp [checkedEdit?, valid] at accepted
    cases accepted
    exact ⟨rfl, rfl⟩
  · simp [checkedEdit?, valid] at accepted

theorem add?_checked (accepted : add? block candidate = some edit) :
    ∃ applied, AddIdealize.step ⟨fun _ => none⟩ block.program candidate = .ok (some applied) ∧
      addRule? applied.rule = some edit.rule ∧ edit.state = fromRewrite block applied.rewrite := by
  cases checked : AddIdealize.step ⟨fun _ => none⟩ block.program candidate with
  | error reason => simp [add?, checked] at accepted
  | ok result =>
    cases result with
    | none => simp [add?, checked] at accepted
    | some applied =>
      simp only [add?, checked, Option.bind_eq_some_iff] at accepted
      obtain ⟨rule, kind, hat⟩ := accepted
      obtain ⟨sameRule, sameState⟩ := checkedEdit_fields hat
      exact ⟨applied, rfl, sameRule ▸ kind, sameState⟩

theorem rightZero?_checked (accepted : rightZero? block candidate = some edit) :
    ∃ applied, AddIdealize.step ⟨fun _ => none⟩ block.program candidate = .ok (some applied) ∧
      applied.rule = .rightZero ∧ edit.rule = .rightZero ∧ edit.state = fromRewrite block applied.rewrite := by
  obtain ⟨found, rule⟩ := Option.filter_eq_some_iff.mp accepted
  have isRightZero : edit.rule = .rightZero := of_decide_eq_true rule
  obtain ⟨applied, checked, kind, state⟩ := add?_checked found
  rw [isRightZero] at kind
  have selected : applied.rule = .rightZero := by
    cases picked : applied.rule <;> simp [addRule?, picked] at kind ⊢
  exact ⟨applied, checked, selected, isRightZero, state⟩

private theorem unused_agrees (accepted : unused? block candidate = some edit)
    (entry : Tuple (Val model.value) (dataPorts inputs)) : Agrees block edit.state entry := by
  obtain ⟨deleted, checked, admitted⟩ := Option.bind_eq_some_iff.mp accepted
  rw [(checkedEdit_fields admitted).2]
  exact ⟨Deletion.delete?_agrees checked model entry PUnit.unit, (Deletion.delete?_eq_some_iff.mp checked).2⟩

theorem unused?_eq_none_iff : unused? block candidate = none ↔
    Deletion.delete? candidate block.packet = none := by
  cases checked : Deletion.delete? candidate block.packet with
  | none => simp [unused?, checked]
  | some deleted =>
    let state : State inputs ports block.sigs :=
      ⟨⟨deleted.erasure.sigs', deleted.erasure.flow, deleted.outputs⟩, deleted.erasure.route⟩
    have kept : List.Sublist (Deletion.opcodes state.block.flow) (Deletion.opcodes block.flow) := by
      change List.Sublist (Deletion.opcodes deleted.erasure.flow) (Deletion.opcodes block.flow)
      rw [Deletion.delete?_opcode_order checked]
      exact List.eraseIdx_sublist _ _
    have adds : addCount state.block ≤ addCount block := kept.countP_le
    have bindings : state.block.sigs.length + 1 = block.sigs.length := deleted.erasure.shorter
    have decreases : weight state.block < weight block := by
      unfold weight
      omega
    simp only [unused?, checked, Option.bind_some]
    change checkedEdit? block .deleteUnused state = none ↔ some deleted = none
    simp [checkedEdit?, Rule.erases, bindings, decreases]

theorem step?_checked (accepted : step? block = some edit) :
    ∃ candidate : Producer block.flow word,
      add? block candidate = some edit ∨ unused? block candidate = some edit := by
  cases found : (RightIdentityPass.wordProducers block.flow).findSome? (add? block) with
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
  · obtain ⟨applied, chosen, _, same⟩ := add?_checked checked
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
      (RightIdentityPass.wordProducers block.flow).findSome? (add? block) = none ∧
        (RightIdentityPass.wordProducers block.flow).findSome? (unused? block) = none := by
    cases first : (RightIdentityPass.wordProducers block.flow).findSome? (add? block) <;> simp [step?, first]
  rw [noFirst, scan_iff, scan_iff]
  exact ⟨fun miss candidate => ⟨miss.1 candidate, miss.2 candidate⟩,
    fun miss => ⟨fun candidate => (miss candidate).1, fun candidate => (miss candidate).2⟩⟩

private theorem run_spec (fuel : Nat) (block : Block inputs ports) (enough : weight block < fuel) :
    let final := Discovery.run fuel block enough
    (final.state.block.sigs.length + final.rules.countP Rule.erases = block.sigs.length ∧
      weight final.state.block + final.rules.length ≤ weight block ∧ NoEligible final.state.block) ∧
      ∀ entry : Tuple (Val model.value) (dataPorts inputs), Agrees block final.state entry := by
  induction fuel generalizing block with
  | zero => exact (Nat.not_lt_zero _ enough).elim
  | succ fuel ih =>
    dsimp only [Discovery.run]
    split
    · rename_i missing
      exact ⟨⟨by simp [initial], by simp [initial], (step?_eq_none_iff block).mp missing⟩,
        fun entry => run_agrees (requests := []) rfl entry⟩
    · rename_i edit checked
      have size := edit.bindingCount
      have smaller := edit.decreases
      obtain ⟨⟨tailSize, tailBudget, stopped⟩, tailAgrees⟩ := ih edit.state.block (by omega)
      refine ⟨⟨?_, ?_, stopped⟩, fun entry => compose_agrees entry (step_agrees checked entry) (tailAgrees entry)⟩
      · simp only [State.compose, List.countP_cons]
        omega
      · simp only [State.compose, List.length_cons]
        omega

theorem normalize_spec (block : Block inputs ports) :
    let final := normalize block
    (final.state.block.sigs.length + final.rules.countP Rule.erases = block.sigs.length ∧
      weight final.state.block + final.rules.length ≤ weight block ∧ NoEligible final.state.block) ∧
      ∀ entry : Tuple (Val model.value) (dataPorts inputs), Agrees block final.state entry :=
  run_spec _ block (Nat.lt_succ_self _)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery
