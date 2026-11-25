module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Tensor.Thms

/-! # Retraction for packed singleton bodies -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReificationPackedBody

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (singletonValueFamily whiskerLeftRegion whiskerLeftRegion_typed)
open Paper.RetainedLet (unpackBody unpackBody_typed)
open Paper.PackedBody

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X A D : τ} {p : Region Φ}

private theorem applyPacked_eq :
    applyPacked p =
      (Region.br 0 (.pair (.var 1) (.var 0))).lsubst
        (fun _ => p.renameVars (lift (Nat.succ ∘ Nat.succ))) := by
  simp only [applyPacked, lsubst, substVars_renameVars]
  congr 1
  funext i
  cases i <;> rfl

theorem applyPacked_typed (hp : ValueBranches [Silmaril.product X A] p [D]) :
    ValueBranches [A, X] (applyPacked p) [D] := by
  rw [applyPacked_eq]
  have hPair : ValueBranches [A, X] (.br 0 (.pair (.var 1) (.var 0)) : Region Φ) [Silmaril.product X A] :=
    .br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))
  have w : Ren ([] : VCtx τ) [A, X] (Nat.succ ∘ Nat.succ) := by
    intro i C hi
    simp [At] at hi
  exact hPair.lsubst (singletonValueFamily (hp.renameVars (w.lift (Silmaril.product X A))))

theorem unpack_applyPacked (hp : ValueBranches [Silmaril.product X A] p [D]) :
    Paper.Eqv [Silmaril.product X A] (unpackBody (applyPacked p)) p [D] := by
  let P := Silmaril.product X A
  have hid : ValueBranches [A] (.br 0 (.var 0) : Region Φ) [A] := .br rfl (.var (i := 0) rfl)
  have hout : ValueBranches [P] (.br 0 (.var 0) : Region Φ) [P] := .br rfl (.var (i := 0) rfl)
  have hbody := (singletonValueFamily hp).liftVars P
  have h := (Paper.whiskerLeftRegion_id (Φ := Φ) X A).lsubstPost
    (whiskerLeftRegion_typed X hid) hout (fun _ _ hi => (hbody hi).hasType)
  change Paper.Eqv [P]
    (compLSubst (fun _ => whiskerLeftRegion (.br 0 (.var 0))) (fun _ => p) 0)
    (compLSubst labelId (fun _ => p) 0) [D] at h
  rw [compLSubst_id_left] at h
  have shape : unpackBody (applyPacked p) =
      compLSubst (fun _ => whiskerLeftRegion (.br 0 (.var 0))) (fun _ => p) 0 := by
    unfold unpackBody applyPacked compLSubst
    change Region.let₂ (.var 0)
      ((p.substVars (Tm.consSubst (.pair (.var 1) (.var 0)) (Tm.var ∘ (Nat.succ ∘ Nat.succ)))).renameVars
        (lift (lift Nat.succ))) =
      (Region.let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0)))).lsubst (liftLSubstVars (fun _ => p))
    simp only [lsubst, liftLSubstVars, renameVars_comp, renameVars_substVars, substVars_renameVars]
    congr 2
    funext i
    cases i <;> rfl
  rw [shape]
  exact h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReificationPackedBody
