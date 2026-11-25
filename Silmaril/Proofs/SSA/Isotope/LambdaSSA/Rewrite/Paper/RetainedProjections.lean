module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs

/-! # Projection after fixed-factor whiskering -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedProjections

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper (Eqv lsubst_singleton_congr)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
  (whiskerLeftRegion whiskerRightRegion whiskerLeftBody whiskerRightBody
    whiskerLeftRegion_typed whiskerRightRegion_typed productFstBranches productSndBranches)

open Silmaril.DeBruijn (lift)

universe u v

variable {Φ : Type v}

private abbrev seq (r s : Region Φ) : Region Φ := compLSubst (fun _ => r) (fun _ => s) 0
private abbrev leftRen : Nat → Nat := lift (Nat.succ ∘ Nat.succ)
private abbrev rightRen : Nat → Nat := Nat.succ ∘ lift Nat.succ
private abbrev fstRegion : Region Φ := .let₂ (.var 0) (.br 0 (.var 1))
private abbrev sndRegion : Region Φ := .let₂ (.var 0) (.br 0 (.var 0))

private theorem left_then_snd (r : Region Φ) :
    seq (whiskerLeftRegion r) sndRegion =
      .let₂ (.var 0) ((r.renameVars leftRen).lsubst (fun _ =>
        .let₂ (.pair (.var 2) (.var 0)) (.br 0 (.var 0)))) := by
  unfold seq whiskerLeftRegion whiskerLeftBody
  rw [compLSubst, lsubst, lsubst_comp]
  rfl

private theorem right_then_fst (r : Region Φ) :
    seq (whiskerRightRegion r) fstRegion =
      .let₂ (.var 0) ((r.renameVars rightRen).lsubst (fun _ =>
        .let₂ (.pair (.var 0) (.var 1)) (.br 0 (.var 1)))) := by
  unfold seq whiskerRightRegion whiskerRightBody
  rw [compLSubst, lsubst, lsubst_comp]
  rfl

private theorem snd_then (r : Region Φ) :
    seq sndRegion r = .let₂ (.var 0) (r.renameVars leftRen) := by
  simp only [compLSubst, lsubst, liftLSubstVars, renameVars_comp, substVars_renameVars]
  rw [renameVars_eq_substVars]
  congr 2
  funext i
  cases i <;> rfl

private theorem fst_then (r : Region Φ) :
    seq fstRegion r = .let₂ (.var 0) (r.renameVars rightRen) := by
  simp only [compLSubst, lsubst, liftLSubstVars, renameVars_comp, substVars_renameVars]
  rw [renameVars_eq_substVars]
  congr 2
  funext i
  cases i <;> rfl

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

private theorem substitute_singleton_identity {Γ : VCtx τ} {A : τ} {r : Region Φ}
    (hr : ValueBranches Γ r [A]) :
    Eqv Γ (r.lsubst (fun _ => .br 0 (.var 0))) r [A] := by
  have h : ∀ ⦃i D⦄, At [A] i D →
      Eqv (D :: Γ) (.br 0 (.var 0) : Region Φ) (labelId i) [A] := by
    intro i D hi
    cases i with
    | zero => exact Eqv.refl (.br hi (.var rfl))
    | succ i => simp [At] at hi
  simpa only [lsubst_labelId] using Eqv.lsubstCongr hr h

private theorem whiskerLeft_snd_region {A B : τ} {r : Region Φ} (X : τ)
    (hr : ValueBranches [A] r [B]) :
    Eqv [product X A] (seq (whiskerLeftRegion r) sndRegion) (seq sndRegion r) [B] := by
  rw [left_then_snd, snd_then]
  apply Eqv.let₂ (A := X) (B := A) (.var rfl)
  have renamed := hr.renameVars ((((Ren.wk [] (product X A)).comp (Ren.wk _ X)).lift A) :
    Ren [A] [A, X, product X A] leftRen)
  apply Eqv.trans (s := (r.renameVars leftRen).lsubst (fun _ => .br 0 (.var 0)))
  · apply lsubst_singleton_congr renamed
    have ha : Tm.BranchValue [B, A, X, product X A] (.var 2 : Tm Φ) X := .var rfl
    have hb : Tm.BranchValue [B, A, X, product X A] (.var 0 : Tm Φ) B := .var rfl
    exact .productBeta (.let₂Beta ha hb (.br rfl (.var (i := 0) rfl)))
  · exact substitute_singleton_identity renamed

private theorem whiskerRight_fst_region {A B : τ} {r : Region Φ} (X : τ)
    (hr : ValueBranches [A] r [B]) :
    Eqv [product A X] (seq (whiskerRightRegion r) fstRegion) (seq fstRegion r) [B] := by
  rw [right_then_fst, fst_then]
  apply Eqv.let₂ (A := A) (B := X) (.var rfl)
  have renamed := hr.renameVars ((((Ren.wk [] (product A X)).lift A).comp (Ren.wk _ X)) :
    Ren [A] [X, A, product A X] rightRen)
  apply Eqv.trans (s := (r.renameVars rightRen).lsubst (fun _ => .br 0 (.var 0)))
  · apply lsubst_singleton_congr renamed
    have ha : Tm.BranchValue [B, X, A, product A X] (.var 0 : Tm Φ) B := .var rfl
    have hb : Tm.BranchValue [B, X, A, product A X] (.var 1 : Tm Φ) X := .var rfl
    exact .productBeta (.let₂Beta ha hb (.br rfl (.var (i := 1) rfl)))
  · exact substitute_singleton_identity renamed

open CategoryTheory
open Paper.TypeCategory

private theorem seq_typed {A B C : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [B] s [C]) : ValueBranches [A] (seq r s) [C] := by
  have left : LSubst.ValueFamily [] [A] [B] (fun _ => r) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hr
  have right : LSubst.ValueFamily [] [B] [C] (fun _ => s) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hs
  exact (left.comp right) (ℓ := 0) rfl

theorem whiskerLeft_productSnd {A B : τ} (X : τ) (f : ofType (Φ := Φ) A ⟶ ofType B) :
    whiskerLeft (ofType X) f ≫ ofRegion (τ := τ) (productSndBranches X B) =
      ofRegion (τ := τ) (productSndBranches X A) ≫ f := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion (A := A) (B := B) f
  rw [whiskerLeft_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _ (seq_typed (whiskerLeftRegion_typed X hr) (productSndBranches X B)),
    ofRegion_comp _ _ (seq_typed (productSndBranches X A) hr)]
  exact (ofRegion_eq_iff _ _).mpr (whiskerLeft_snd_region X hr)

theorem whiskerRight_productFst {A B : τ} (X : τ) (f : ofType (Φ := Φ) A ⟶ ofType B) :
    whiskerRight f (ofType X) ≫ ofRegion (τ := τ) (productFstBranches B X) =
      ofRegion (τ := τ) (productFstBranches A X) ≫ f := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion (A := A) (B := B) f
  rw [whiskerRight_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _ (seq_typed (whiskerRightRegion_typed X hr) (productFstBranches B X)),
    ofRegion_comp _ _ (seq_typed (productFstBranches A X) hr)]
  exact (ofRegion_eq_iff _ _).mpr (whiskerRight_fst_region X hr)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedProjections
