module

public import Silmaril.SSA.SeaOfNodes.Pure.WordNormalize.Defs
import Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Pass.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.WordNormalize
open scoped Silmaril.SSA.SeaOfNodes.Pure.WordNormalize
open Diamond (Val ValueSort dataPorts)
open SubZero (model)
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program next : Program SubZero.Opcode inputs out}

theorem step_none_iff (program : Program SubZero.Opcode inputs out) :
    step? program = none ↔ Normal program := by
  rw [Normal, ← RightIdentityPass.step?_eq_none_iff, ← GVN.Pass.step?_eq_none_iff]
  cases identity : RightIdentityPass.step? program <;>
    simp [step?, gvnStep?, identity, Option.orElse]

private theorem step_properties (accepted : step? program = some next) :
    next.sigs.length + 1 = program.sigs.length ∧
      ∀ entry : Tuple (Val model.value) (dataPorts inputs),
        next.eval model entry = program.eval model entry := by
  cases identity : RightIdentityPass.step? program with
  | some result =>
    simp only [step?, identity, Option.orElse_some, Option.some.injEq] at accepted
    subst next
    exact ⟨RightIdentityPass.step_size identity, RightIdentityPass.step_eval_eq identity⟩
  | none =>
    simp only [step?, identity, Option.orElse_none, gvnStep?, Option.map_eq_some_iff] at accepted
    obtain ⟨rewrite, found, rfl⟩ := accepted
    exact ⟨GVN.Pass.step_size found, fun entry =>
      (GVN.Pass.step_sound found model entry PUnit.unit _ program.result).symm⟩

theorem step_size (accepted : step? program = some next) :
    next.sigs.length + 1 = program.sigs.length :=
  (step_properties accepted).1

theorem step_eval_eq (accepted : step? program = some next)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    next.eval model entry = program.eval model entry :=
  (step_properties accepted).2 entry

theorem normalize_count (program : Program SubZero.Opcode inputs out) :
    let final := normalize program
    final.program.sigs.length + final.deletions = program.sigs.length ∧
      final.deletions ≤ program.sigs.length :=
  RightIdentityPass.runWith_progress step? _ program (fun h => step_size h)

theorem normalize_normal (program : Program SubZero.Opcode inputs out) :
    Normal (normalize program).program :=
  (step_none_iff _).1 (RightIdentityPass.runWith_stopped step? _ program (fun h => step_size h) (Nat.le_refl _))

theorem normalize_eval_eq (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (normalize program).program.eval model entry = program.eval model entry :=
  RightIdentityPass.runWith_eval_eq step? _ program (fun h => step_eval_eq h) entry

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize
