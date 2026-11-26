module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Separation

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB
open Silmaril.Isotope.Institution.Observational

universe u v w x

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

theorem noLocalBlocks_not_scoped {r : Region Φ} (h : r.NoLocalBlocks) {vars : Nat} :
    ¬ r.Scoped 0 vars := by
  induction r generalizing vars with
  | br _ _ => exact fun scope => Nat.not_lt_zero _ scope.1
  | let₁ _ _ ih | let₂ _ _ ih => exact fun scope => ih h scope.2
  | case _ _ _ ih _ => exact fun scope => ih h.1 scope.2.1
  | cfg _ _ _ ih _ =>
    obtain ⟨rfl, entry⟩ := h
    exact fun scope => ih entry scope.1

theorem no_common_upper_bound (Γ : VCtx τ) (L : LCtx τ) (f : Φ)
    (source : instrSrc f = (unit : τ)) :
    ¬ ∃ r : Typed (Φ := Φ) Γ L,
      observe (faultModel.{u,w,x} Φ Γ.length) (primitiveThenLoop Γ L f source) ⊆
        observe (faultModel.{u,w,x} Φ Γ.length) r ∧
      observe (faultModel.{u,w,x} Φ Γ.length) (loop Γ L) ⊆
        observe (faultModel.{u,w,x} Φ Γ.length) r := by
  rintro ⟨r, boundsFault, boundsLoop⟩
  have hf := boundsFault (a := .fault PUnit.unit PUnit.unit)
    (show _ from Region.Fault.let₁_arg (.op_fault .unit trivial))
  have hd := boundsLoop (a := .diverge PUnit.unit)
    (show _ from External.Diverges.of_internal (cfg_self_loop _ _))
  change Region.Fault _ _ _ _ _ _ at hf
  change External.Diverges _ (fun _ _ _ => False) _ at hd
  exact fault_not_diverges (by intro f a s v s' v' s'' step _; exact False.elim step)
    (fun _ step => False.elim step) hf (External.Diverges.false_iff.mp hd)

theorem observe_subset_empty {Γ : VCtx τ} (M : Model.{u,w,x} Φ Γ.length)
    (r : Typed (Φ := Φ) Γ []) :
    observe M r ⊆ emptyObservations M.α M.σ := by
  intro o ho
  cases o with
  | ret _ _ _ =>
    exact Nat.not_lt_zero _ (r.property.scoped.eval_label_lt (ret_mem_ssaBeh.mp ho))
  | fault _ _ | diverge _ => trivial

theorem observe_primitiveThenLoop_eq_empty {Γ : VCtx τ} (M : Model.{u,w,x} Φ Γ.length)
    (f : Φ) (source : instrSrc f = (unit : τ))
    (faults : ∀ s s', M.faults f .unit s s')
    (continues : ∀ s, M.prim f .unit s ∨ ∃ value s', M.instr f .unit s value s') :
    observe M (primitiveThenLoop Γ [] f source) = emptyObservations M.α M.σ := by
  apply Set.Subset.antisymm (observe_subset_empty M _)
  intro o ho
  cases o with
  | ret _ _ _ => exact ho.elim
  | fault s s' => exact Region.Fault.let₁_arg (.op_fault .unit (faults s s'))
  | diverge s =>
    rcases continues s with div | ⟨_, _, step⟩
    · exact External.Diverges.fold (.let₁_arg (.primitive .unit div))
    · exact External.Diverges.fold_core
        (.let₁ (.op .unit step) (External.Diverges.of_internal (cfg_self_loop _ _)))

end Silmaril.Proofs.Isotope.LambdaSSA.UB
