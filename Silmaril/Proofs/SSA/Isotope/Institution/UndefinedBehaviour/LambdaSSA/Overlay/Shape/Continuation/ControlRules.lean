module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeSubstitution
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA (Region)

universe u v w x

variable {Φ : Type u} {α : Type w} {σ : Type x} {O : Ops Φ α σ} {env : Env α}

theorem cfgOutward (r : LambdaSSA.Region Φ) (n : Nat) (blocks : Fin n → LambdaSSA.Region Φ) :
    RegionAt O env (.cfg (r.renameLabels (n + ·)) n blocks) env r where
  eval := by
    intro s i a t
    constructor
    · intro run
      cases run with
      | cfg head tail =>
        obtain ⟨j, same, original⟩ := Semantics.Region.Eval.of_renameLabels head
        subst same
        cases tail with
        | exit _ => simpa only [Nat.add_sub_cancel_left] using original
        | step inside _ _ => omega
    · intro run
      exact .cfg (run.renameLabels (n + ·)) (by
        simpa only [Nat.add_sub_cancel_left] using
          (Semantics.Region.Follow.exit (blocks := blocks) (Nat.le_add_right n i)))
  fault := by
    intro s t
    constructor
    · intro run
      cases run with
      | cfg_entry failure => exact failure.of_renameLabels
      | cfg_follow head tail =>
        obtain ⟨_, same, _⟩ := Semantics.Region.Eval.of_renameLabels head
        cases tail <;> omega
    · exact fun run => .cfg_entry (run.renameLabels (n + ·))
  div := by
    intro s
    constructor
    · intro run
      cases run.unfold with
      | core step =>
        cases step with
        | cfg_entry div => exact (External.Diverges.renameLabels_iff _).mp div
        | cfg_follow head tail =>
          obtain ⟨_, same, _⟩ := Semantics.Region.Eval.of_renameLabels head
          cases tail.unfold with
          | core step => cases step <;> omega
    · exact fun run => .fold_core (.cfg_entry ((External.Diverges.renameLabels_iff _).mpr run))

variable {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ L : List τ}
  {A B : τ} {e : LambdaSSA.Tm Φ} {l r : LambdaSSA.Region Φ}

private def caseEntry (h : e.HasType Γ (coprod A B)) : UB.Typed (Φ := Φ) Γ [A, B] :=
  ⟨.case e (.br 0 (.var 0)) (.br 1 (.var 0)),
    .case h (.br (ℓ := 0) rfl (.var (i := 0) rfl)) (.br (ℓ := 1) rfl (.var (i := 0) rfl))⟩

private def caseArms (hl : l.HasType (A :: Γ) L) (hr : r.HasType (B :: Γ) L) :
    (i : Fin ([A, B] : List τ).length) → UB.Typed (Φ := Φ) (([A, B] : List τ).get i :: Γ) L :=
  fun i => ⟨Fin.cases l (fun _ => r) i, Fin.cases hl (fun j => Fin.eq_zero j ▸ hr) i⟩

private theorem case_entry_eval {s t : σ} {i : Fin 2} {v : Value α}
    (h : e.HasType Γ (coprod A B)) :
    Semantics.Region.Eval O.instr env (caseEntry h).val s i v t ↔
      (i = 0 ∧ Semantics.Tm.Eval O.instr env e s (.inl v) t) ∨
        (i = 1 ∧ Semantics.Tm.Eval O.instr env e s (.inr v) t) := by
  constructor
  · intro run
    change Semantics.Region.Eval O.instr env (.case e (.br 0 (.var 0)) (.br 1 (.var 0))) s i v t at run
    generalize labelEq : i.val = label at run
    cases run with
    | case_inl arg body =>
      cases body with
      | br body => cases body; exact Or.inl ⟨Fin.ext labelEq, arg⟩
    | case_inr arg body =>
      cases body with
      | br body => cases body; exact Or.inr ⟨Fin.ext labelEq, arg⟩
  · rintro (⟨rfl, arg⟩ | ⟨rfl, arg⟩)
    · exact .case_inl arg (.br .var)
    · exact .case_inr arg (.br .var)

private theorem case_entry_fault {s t : σ} (h : e.HasType Γ (coprod A B)) :
    Semantics.Region.Fault O.instr O.faults env (caseEntry h).val s t ↔
      Semantics.Tm.Fault O.instr O.faults env e s t := by
  constructor
  · intro run
    change Semantics.Region.Fault O.instr O.faults env
      (.case e (.br 0 (.var 0)) (.br 1 (.var 0))) s t at run
    cases run with
    | case_arg fault => exact fault
    | case_inl _ fault | case_inr _ fault =>
      cases fault with | br fault => cases fault
  · exact Semantics.Region.Fault.case_arg

private theorem case_entry_div {s : σ} (h : e.HasType Γ (coprod A B)) :
    External.Diverges O.instr O.prim (.region env (caseEntry h).val s) ↔
      Semantics.Tm.ExternalDiverges O.instr O.prim env e s := by
  constructor
  · intro run
    change External.Diverges O.instr O.prim (.region env (.case e (.br 0 (.var 0)) (.br 1 (.var 0))) s) at run
    cases run.unfold with
    | case_arg arg => exact arg
    | core step =>
      cases step with
      | case_inl _ branch | case_inr _ branch =>
        cases branch.unfold with
        | core step => cases step
        | br arg => cases arg
  · exact fun run => .fold (.case_arg run)

/-- Case-to-CFG uses a one-shot label substitution with two outward arms. -/
theorem caseCfg (he : e.HasType Γ (coprod A B)) (hl : l.HasType (A :: Γ) L) (hr : r.HasType (B :: Γ) L) :
    RegionAt O env (.case e l r) env (LambdaSSA.Region.caseCfg e l r) where
  eval := by
    intro s i v t
    change _ ↔ Semantics.Region.Eval O.instr env (nativeLsubst (caseEntry he) (caseArms hl hr)) s i v t
    rw [nativeLsubst_eval_iff]
    constructor
    · intro run
      cases run with
      | case_inl head body => exact ⟨0, _, _, (case_entry_eval he).mpr (.inl ⟨rfl, head⟩), body⟩
      | case_inr head body => exact ⟨1, _, _, (case_entry_eval he).mpr (.inr ⟨rfl, head⟩), body⟩
    · rintro ⟨j, a, mid, head, body⟩
      rcases (case_entry_eval he).mp head with ⟨rfl, arg⟩ | ⟨rfl, arg⟩
      · exact .case_inl arg body
      · exact .case_inr arg body
  fault := by
    intro s t
    change _ ↔ Semantics.Region.Fault O.instr O.faults env (nativeLsubst (caseEntry he) (caseArms hl hr)) s t
    rw [nativeLsubst_fault_iff]
    constructor
    · intro run
      cases run with
      | case_arg head => exact .inl ((case_entry_fault he).mpr head)
      | case_inl head body => exact .inr ⟨0, _, _, (case_entry_eval he).mpr (.inl ⟨rfl, head⟩), body⟩
      | case_inr head body => exact .inr ⟨1, _, _, (case_entry_eval he).mpr (.inr ⟨rfl, head⟩), body⟩
    · rintro (head | ⟨j, a, mid, head, body⟩)
      · exact .case_arg ((case_entry_fault he).mp head)
      · rcases (case_entry_eval he).mp head with ⟨rfl, arg⟩ | ⟨rfl, arg⟩
        · exact .case_inl arg body
        · exact .case_inr arg body
  div := by
    intro s
    change _ ↔ External.Diverges O.instr O.prim (.region env (nativeLsubst (caseEntry he) (caseArms hl hr)) s)
    rw [nativeLsubst_diverges_iff]
    constructor
    · intro run
      cases run.unfold with
      | case_arg head => exact .inl ((case_entry_div he).mpr head)
      | core step =>
        cases step with
        | case_inl head body => exact .inr ⟨0, _, _, (case_entry_eval he).mpr (.inl ⟨rfl, head⟩), body⟩
        | case_inr head body => exact .inr ⟨1, _, _, (case_entry_eval he).mpr (.inr ⟨rfl, head⟩), body⟩
    · rintro (head | ⟨j, a, mid, head, body⟩)
      · exact .fold (.case_arg ((case_entry_div he).mp head))
      · rcases (case_entry_eval he).mp head with ⟨rfl, arg⟩ | ⟨rfl, arg⟩
        · exact .fold_core (.case_inl arg body)
        · exact .fold_core (.case_inr arg body)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation
