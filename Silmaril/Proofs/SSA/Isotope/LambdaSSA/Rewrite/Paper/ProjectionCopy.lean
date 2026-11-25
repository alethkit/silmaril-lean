module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Copy.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # Copying the components of an unpacked product -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCopy

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.TypeCategory
open CfgEta.TypeCategory (productFstBranches productSndBranches whiskerLeftRegion whiskerRightRegion
  whiskerLeftRegion_typed whiskerRightRegion_typed seqValueBranches)
open Paper (Eqv)
open Paper.RetainedLet (diagonal_typed)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B D : τ}

set_option backward.isDefEq.respectTransparency false in
private theorem copyProjection {r : Region Φ} (hr : ValueBranches [product A B] r [D])
    (h : r = .let₂ (.var 0) (.br 0 (.var 0)) ∧ D = B ∨
      r = .let₂ (.var 0) (.br 0 (.var 1)) ∧ D = A) :
    PreservesDiagonal (ofRegion hr) := by
  change pairArrows (ofRegion hr) (ofRegion hr) = ofRegion hr ≫ diagonalArrow D
  unfold pairArrows diagonalArrow
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion]
  unfold tensorObj
  let ht := seqValueBranches (diagonal_typed (product A B)) (seqValueBranches
    (whiskerRightRegion_typed (product A B) hr) (whiskerLeftRegion_typed D hr))
  let hs := seqValueBranches hr (diagonal_typed D)
  erw [ofRegion_comp _ _ (seqValueBranches (whiskerRightRegion_typed (product A B) hr) (whiskerLeftRegion_typed D hr)),
    ofRegion_comp _ _ ht, ofRegion_comp _ _ hs]
  apply (ofRegion_eq_iff ht hs).mpr
  apply (Paper.product_variable_eta_iff (i := 0) (A := A) (B := B)
    (rfl : At [product A B] 0 (product A B)) ht.hasType hs.hasType).mp
  let Δ : VCtx τ := [B, A, product A B]
  have x : Tm.BranchValue Δ (.var 1 : Tm Φ) A := .var rfl
  have y : Tm.BranchValue Δ (.var 0 : Tm Φ) B := .var rfl
  have xy := Tm.BranchValue.pair x y
  -- In the unpacked context, both composites just return two copies of the selected component.
  rcases h with ⟨shape, type⟩ | ⟨shape, type⟩ <;> subst r <;> subst D
  · change Eqv Δ (.let₂ (.pair (.pair (.var 1) (.var 0)) (.pair (.var 1) (.var 0)))
      (.let₂ (.var 1) (.let₂ (.pair (.var 0) (.var 2))
        (.let₂ (.var 0) (.br 0 (.pair (.var 3) (.var 0)))))))
      (.let₂ (.pair (.var 1) (.var 0)) (.br 0 (.pair (.var 0) (.var 0)))) [product B B]
    apply Eqv.trans _ (.symm (.productBeta (.let₂Beta x y
      (.br rfl (.pair (.var (i := 0) rfl) (.var (i := 0) rfl))))))
    refine Eqv.trans (.productBeta (.let₂Beta xy xy
      (.let₂ (A := A) (B := B) (.var rfl)
        (.let₂ (A := B) (B := product A B) (.pair (.var rfl) (.var rfl))
          (.let₂ (A := A) (B := B) (.var rfl)
            (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 0) rfl)))))))) ?_
    refine Eqv.trans (.productBeta (.let₂Beta x y
      (.let₂ (A := B) (B := product A B) (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))
        (.let₂ (A := A) (B := B) (.var rfl)
          (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 0) rfl))))))) ?_
    refine Eqv.trans (.productBeta (.let₂Beta y xy
      (.let₂ (A := A) (B := B) (.var rfl)
        (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 0) rfl)))))) ?_
    exact .productBeta (.let₂Beta x y (.br rfl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))))
  · change Eqv Δ (.let₂ (.pair (.pair (.var 1) (.var 0)) (.pair (.var 1) (.var 0)))
      (.let₂ (.var 1) (.let₂ (.pair (.var 1) (.var 2))
        (.let₂ (.var 0) (.br 0 (.pair (.var 3) (.var 1)))))))
      (.let₂ (.pair (.var 1) (.var 0)) (.br 0 (.pair (.var 1) (.var 1)))) [product A A]
    apply Eqv.trans _ (.symm (.productBeta (.let₂Beta x y
      (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 1) rfl))))))
    refine Eqv.trans (.productBeta (.let₂Beta xy xy
      (.let₂ (A := A) (B := B) (.var rfl)
        (.let₂ (A := A) (B := product A B) (.pair (.var rfl) (.var rfl))
          (.let₂ (A := A) (B := B) (.var rfl)
            (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 1) rfl)))))))) ?_
    refine Eqv.trans (.productBeta (.let₂Beta x y
      (.let₂ (A := A) (B := product A B) (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))
        (.let₂ (A := A) (B := B) (.var rfl)
          (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 1) rfl))))))) ?_
    refine Eqv.trans (.productBeta (.let₂Beta x xy
      (.let₂ (A := A) (B := B) (.var rfl)
        (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 1) rfl)))))) ?_
    exact .productBeta (.let₂Beta x y (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 1) rfl))))

theorem preservesDiagonal_productFst (A B : τ) :
    PreservesDiagonal (ofRegion (productFstBranches (Φ := Φ) A B)) :=
  copyProjection (productFstBranches A B) (.inr ⟨rfl, rfl⟩)

theorem preservesDiagonal_productSnd (A B : τ) :
    PreservesDiagonal (ofRegion (productSndBranches (Φ := Φ) A B)) :=
  copyProjection (productSndBranches A B) (.inl ⟨rfl, rfl⟩)


end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCopy
