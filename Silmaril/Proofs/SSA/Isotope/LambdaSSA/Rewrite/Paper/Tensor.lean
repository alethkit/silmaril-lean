module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Thms

/-! # Composition of singleton whiskering in the typed paper relation -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Tensor

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper (Eqv lsubst_singleton_congr)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
open Silmaril.DeBruijn (lift)

variable {Φ : Type v}

private def seqRegion (r s : Region Φ) : Region Φ :=
  r.lsubst (fun _ => s.renameVars (lift Nat.succ))

private abbrev leftRen : Nat → Nat := lift (Nat.succ ∘ Nat.succ)
private abbrev rightRen : Nat → Nat := Nat.succ ∘ lift Nat.succ
private abbrev leftPair : Tm Φ := .pair (.var 2) (.var 0)
private abbrev rightPair : Tm Φ := .pair (.var 0) (.var 1)
private abbrev repackLeft : Nat → Region Φ := fun _ => .br 0 leftPair
private abbrev repackRight : Nat → Region Φ := fun _ => .br 0 rightPair

-- Composition adds the original input and its two unpacked components
-- plus the intermediate result. The inner unpacking keeps its first three slots.
private abbrev liftCapture : Nat → Nat := Silmaril.DeBruijn.liftN 2 (lift Nat.succ)
private abbrev fourCaptures : Nat → Nat := liftCapture ∘ liftCapture ∘ liftCapture ∘ liftCapture

private abbrev afterLeft (s : Region Φ) : Region Φ :=
  (whiskerLeftBody s).renameVars fourCaptures
private abbrev afterRight (s : Region Φ) : Region Φ :=
  (whiskerRightBody s).renameVars fourCaptures

private theorem left_twice (r s : Region Φ) :
    seqRegion (whiskerLeftRegion r) (whiskerLeftRegion s) =
      .let₂ (.var 0) ((r.renameVars leftRen).lsubst
        (fun _ => .let₂ leftPair ((afterLeft s).substVars
          (Tm.liftSubst (Tm.liftSubst (Tm.singleSubst leftPair)))))) := by
  unfold seqRegion whiskerLeftRegion whiskerLeftBody
  rw [lsubst, lsubst_comp]
  congr 2
  funext i
  simp only [compLSubst, lsubst, liftLSubstVars, renameVars, Tm.rename, lift, substVars,
    Tm.subst, Tm.singleSubst, Tm.consSubst, renameVars_comp]
  rfl

private theorem right_twice (r s : Region Φ) :
    seqRegion (whiskerRightRegion r) (whiskerRightRegion s) =
      .let₂ (.var 0) ((r.renameVars rightRen).lsubst
        (fun _ => .let₂ rightPair ((afterRight s).substVars
          (Tm.liftSubst (Tm.liftSubst (Tm.singleSubst rightPair)))))) := by
  unfold seqRegion whiskerRightRegion whiskerRightBody
  rw [lsubst, lsubst_comp]
  congr 2
  funext i
  simp only [compLSubst, lsubst, liftLSubstVars, renameVars, Tm.rename, lift, substVars,
    Tm.subst, Tm.singleSubst, Tm.consSubst, renameVars_comp]
  rfl

private def unpackPair (a b : Tm Φ) : Nat → Tm Φ :=
  Tm.consSubst b (Tm.singleSubst a)

private theorem left_once (r s : Region Φ) :
    whiskerLeftRegion (seqRegion r s) = .let₂ (.var 0) ((r.renameVars leftRen).lsubst
      (fun _ => (s.renameVars (lift leftRen ∘ lift Nat.succ)).lsubst (liftLSubstVars repackLeft))) := by
  simp only [whiskerLeftRegion, whiskerLeftBody, seqRegion, renameVars_lsubst, renameVars_comp, lsubst_comp]
  rfl

private theorem right_once (r s : Region Φ) :
    whiskerRightRegion (seqRegion r s) = .let₂ (.var 0) ((r.renameVars rightRen).lsubst
      (fun _ => (s.renameVars (lift rightRen ∘ lift Nat.succ)).lsubst (liftLSubstVars repackRight))) := by
  simp only [whiskerRightRegion, whiskerRightBody, seqRegion, renameVars_lsubst, renameVars_comp, lsubst_comp]
  rfl

private theorem left_beta_body (s : Region Φ) :
    ((afterLeft s).substVars (Tm.liftSubst (Tm.liftSubst (Tm.singleSubst leftPair)))).substVars
      (unpackPair (.var 2) (.var 0)) =
      (s.renameVars (lift leftRen ∘ lift Nat.succ)).lsubst (liftLSubstVars repackLeft) := by
  simp only [afterLeft, whiskerLeftBody, substVars_comp, substVars_renameVars, substVars_lsubst]
  rw [renameVars_eq_substVars]
  congr 2
  funext i
  cases i <;> rfl

private theorem right_beta_body (s : Region Φ) :
    ((afterRight s).substVars (Tm.liftSubst (Tm.liftSubst (Tm.singleSubst rightPair)))).substVars
      (unpackPair (.var 0) (.var 1)) =
      (s.renameVars (lift rightRen ∘ lift Nat.succ)).lsubst (liftLSubstVars repackRight) := by
  simp only [afterRight, whiskerRightBody, substVars_comp, substVars_renameVars, substVars_lsubst]
  rw [renameVars_eq_substVars]
  congr 2
  funext i
  cases i <;> rfl

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

omit [TypeFormers τ] in
private theorem insertFourCaptures_typed (P Q R S a b c : τ) :
    Ren [a, b, c] [a, b, c, P, Q, R, S] fourCaptures :=
  let p₁ := (((Ren.wk [] S).lift c).lift b).lift a
  let p₂ := (((Ren.wk [S] R).lift c).lift b).lift a
  let p₃ := (((Ren.wk [R, S] Q).lift c).lift b).lift a
  let p₄ := (((Ren.wk [Q, R, S] P).lift c).lift b).lift a
  p₁.comp (p₂.comp (p₃.comp p₄))

private theorem leftTypedRen (X A : τ) : Ren [A] [A, X, Silmaril.product X A] leftRen :=
  ((Ren.wk [] (Silmaril.product X A)).comp (Ren.wk _ X)).lift A

private theorem rightTypedRen (X A : τ) : Ren [A] [X, A, Silmaril.product A X] rightRen :=
  ((Ren.wk [] (Silmaril.product A X)).lift A).comp (Ren.wk _ X)

variable {A B C : τ} {r s : Region Φ}

/-- Composition uses the shared root generator in a continuation and then under unpacking. -/
theorem whiskerLeftRegion_comp (X : τ)
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [B] s [C]) :
    Eqv [Silmaril.product X A]
      (compLSubst (fun _ => whiskerLeftRegion r) (fun _ => whiskerLeftRegion s) 0)
      (whiskerLeftRegion (compLSubst (fun _ => r) (fun _ => s) 0)) [Silmaril.product X C] := by
  change Eqv [Silmaril.product X A] (seqRegion (whiskerLeftRegion r) (whiskerLeftRegion s))
    (whiskerLeftRegion (seqRegion r s)) [Silmaril.product X C]
  rw [left_twice, left_once]
  apply Eqv.let₂ (A := X) (B := A) (Tm.HasType.var (i := 0) rfl)
  apply lsubst_singleton_congr (hr.renameVars (leftTypedRen X A))
  rw [← left_beta_body]
  have pairLeft : Tm.BranchValue [B, A, X, Silmaril.product X A] (.var 2 : Tm Φ) X := .var rfl
  have pairRight : Tm.BranchValue [B, A, X, Silmaril.product X A] (.var 0 : Tm Φ) B := .var rfl
  apply Eqv.productBeta
  apply ProductBeta.Step.let₂Beta pairLeft pairRight
  have body := whiskerLeftBody_typed X hs
  have shifted := body.renameVars (insertFourCaptures_typed B A X (Silmaril.product X A) B X (Silmaril.product X B))
  exact shifted.hasType.substVars (((Tm.Subst.HasType.single
    (Tm.HasType.pair pairLeft.hasType pairRight.hasType)).lift X).lift B)

/-- Composition uses the shared root generator in a continuation and then under unpacking. -/
theorem whiskerRightRegion_comp (X : τ)
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [B] s [C]) :
    Eqv [Silmaril.product A X]
      (compLSubst (fun _ => whiskerRightRegion r) (fun _ => whiskerRightRegion s) 0)
      (whiskerRightRegion (compLSubst (fun _ => r) (fun _ => s) 0)) [Silmaril.product C X] := by
  change Eqv [Silmaril.product A X] (seqRegion (whiskerRightRegion r) (whiskerRightRegion s))
    (whiskerRightRegion (seqRegion r s)) [Silmaril.product C X]
  rw [right_twice, right_once]
  apply Eqv.let₂ (A := A) (B := X) (Tm.HasType.var (i := 0) rfl)
  apply lsubst_singleton_congr (hr.renameVars (rightTypedRen X A))
  rw [← right_beta_body]
  have pairLeft : Tm.BranchValue [B, X, A, Silmaril.product A X] (.var 0 : Tm Φ) B := .var rfl
  have pairRight : Tm.BranchValue [B, X, A, Silmaril.product A X] (.var 1 : Tm Φ) X := .var rfl
  apply Eqv.productBeta
  apply ProductBeta.Step.let₂Beta pairLeft pairRight
  have body := whiskerRightBody_typed X hs
  have shifted := body.renameVars (insertFourCaptures_typed B X A (Silmaril.product A X) X B (Silmaril.product B X))
  exact shifted.hasType.substVars (((Tm.Subst.HasType.single
    (Tm.HasType.pair pairLeft.hasType pairRight.hasType)).lift B).lift X)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Tensor
