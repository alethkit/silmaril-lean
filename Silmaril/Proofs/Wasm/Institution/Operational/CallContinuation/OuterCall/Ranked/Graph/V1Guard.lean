module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Typing

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs

open Execution.Runtime (FuncAddr)

@[simp] private theorem codeV1_append (left right : List Op) :
    codeV1 (left ++ right) = (codeV1 left && codeV1 right) := by
  induction left with
  | nil => rfl
  | cons op rest ih => simp [codeV1, ih, Bool.and_assoc]

private theorem afterBlock_v1 {saved result rest next kind}
    (outside : codeV1 rest = true) (inside : next.supportsV1 = true) (guard : kind.supportsV1 = true) :
    (Phase.afterBlock saved result rest next kind).supportsV1 = true := by
  cases next with
  | label locals body =>
    cases kind <;> simp_all [Phase.afterBlock, Phase.supportsV1, Body.underLabel, Body.supportsV1, LabelKind.supportsV1]
  | exit locals result =>
    cases result <;> simp [Phase.afterBlock, Phase.supportsV1, Body.supportsV1, outside]
  | _ => simp_all [Phase.afterBlock, Phase.supportsV1, Body.supportsV1, codeV1, Op.supportsV1]

private theorem layer_v1 {fn : Function} {childStep : CallTarget → Phase → Phase → Prop}
    (code : codeV1 fn.code = true)
    (child : ∀ target ∈ fn.targets, ∀ {a b}, childStep target a b →
      a.supportsV1 = true → b.supportsV1 = true)
    {a b kind} (move : Layer fn childStep a b kind) :
    kind.supportsV1 = true → a.supportsV1 = true → b.supportsV1 = true := by
  induction move with
  | numeric step =>
    cases step <;> simp [Phase.supportsV1, Body.afterNumeric, Body.supportsV1, codeV1, Op.supportsV1]
  | ifSelect _ _ cond _ _ _ _ =>
    intro _ supported
    simp only [Phase.supportsV1, Body.supportsV1, codeV1, Op.supportsV1, Bool.and_eq_true_iff] at supported ⊢
    exact ⟨by split; exact supported.1.2; exact supported.1.1, supported.2⟩
  | blockStep _ _ _ _ ih =>
    intro _ supported
    obtain ⟨inner, outer⟩ := Bool.and_eq_true_iff.mp supported
    exact afterBlock_v1 outer (ih rfl inner) rfl
  | loopStep _ _ _ _ _ ih =>
    intro _ supported
    obtain ⟨first, outer⟩ := Bool.and_eq_true_iff.mp supported
    obtain ⟨original, inner⟩ := Bool.and_eq_true_iff.mp first
    exact afterBlock_v1 outer (ih original inner) original
  | @child kind locals saved target rest a b used live step =>
    intro _ supported
    obtain ⟨live, rest⟩ := Bool.and_eq_true_iff.mp supported
    have next := child target used step live
    cases b <;> simp_all [Phase.supportsV1, Body.supportsV1, Body.attach]
    case done result =>
      cases result <;> simp_all [Body.supportsV1]
  | discard cut =>
    cases cut
    simp [Phase.supportsV1, Body.supportsV1, codeV1_append]
  | branchIf _ _ condition _ _ _ =>
    intro _ supported
    split <;> simpa [Phase.supportsV1, Body.supportsV1, codeV1, Op.supportsV1] using supported
  | branchHere =>
    rename_i kind _ _ _ _ _ _
    cases kind <;> simp [LabelKind.branchHere, LabelKind.supportsV1, Phase.supportsV1]; intros; assumption
  | _ =>
    simp [Phase.supportsV1, Body.supportsV1, codeV1, Op.supportsV1, code]

theorem edge_v1 {program : Program} (checked : program.checkV1 = true)
    (address : FuncAddr) :
    ∀ {fn a b}, program.lookup address = some fn →
      program.Edge (Bool.and_eq_true_iff.mp checked).1 address a b →
        a.supportsV1 = true → b.supportsV1 = true := by
  have check := (Bool.and_eq_true_iff.mp checked).1
  induction address using (program.table.wellFounded (Program.rankCheck check)).induction with
  | h address ih =>
    intro fn a b found move supported
    apply layer_v1 (checked_v1_function checked found).2 ?_ ((edge_iff check found).mp move) rfl supported
    intro target used c d child supported
    obtain ⟨callee, childFound, _, _⟩ := linked_target check found used
    exact ih target.address (target_resolved check found used) childFound child supported

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs
