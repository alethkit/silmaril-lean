module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms

/-! # Repacking the two projections of a singleton product -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductRepack

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory
open CfgEta.TypeCategory
  (productFstBranches productSndBranches whiskerLeftRegion whiskerRightRegion
    whiskerLeftRegion_typed whiskerRightRegion_typed)
open Paper (Eqv splitProduct)
open CategoryTheory

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
local notation "obj" => Paper.TypeCategory.ofType (Φ := Φ)

private abbrev seq (r s : Region Φ) : Region Φ := compLSubst (fun _ => r) (fun _ => s) 0
private abbrev fstRegion : Region Φ := .let₂ (.var 0) (.br 0 (.var 1))
private abbrev sndRegion : Region Φ := .let₂ (.var 0) (.br 0 (.var 0))

private theorem seqBranches {X A B : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [A]) (hs : ValueBranches [A] s [B]) :
    ValueBranches [X] (seq r s) [B] :=
  have left : LSubst.ValueFamily [] [X] [A] (fun _ => r) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hr
  have right : LSubst.ValueFamily [] [A] [B] (fun _ => s) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hs
  (left.comp right) (ℓ := 0) rfl

private abbrev repackRegion : Region Φ := seq (Paper.RetainedLet.diagonal : Region Φ)
  (seq (whiskerRightRegion fstRegion) (whiskerLeftRegion sndRegion))

private theorem repack_typed (A B : τ) :
    ValueBranches [product A B] (repackRegion : Region Φ) [product A B] :=
  seqBranches (Paper.RetainedLet.diagonal_typed (product A B))
    (seqBranches (whiskerRightRegion_typed (product A B) (productFstBranches A B))
      (whiskerLeftRegion_typed A (productSndBranches A B)))

private theorem repack_eqv (A B : τ) :
    Eqv [product A B] (repackRegion : Region Φ) (.br 0 (.var 0)) [product A B] := by
  apply (Paper.product_variable_eta_iff (i := 0) (A := A) (B := B)
    (rfl : At [product A B] 0 (product A B)) (repack_typed A B).hasType (.br rfl (.var rfl))).mp
  let Δ : VCtx τ := [B, A, product A B]
  have a : Tm.BranchValue Δ (.var 1 : Tm Φ) A := .var rfl
  have b : Tm.BranchValue Δ (.var 0 : Tm Φ) B := .var rfl
  have p := Tm.BranchValue.pair a b
  -- The four lets open the copied input, the first projection, and the second projection.
  change Eqv Δ (.let₂ (.pair (.pair (.var 1) (.var 0)) (.pair (.var 1) (.var 0)))
    (.let₂ (.var 1) (.let₂ (.pair (.var 1) (.var 2))
      (.let₂ (.var 0) (.br 0 (.pair (.var 3) (.var 0)))))))
    (.br 0 (.pair (.var 1) (.var 0))) [product A B]
  refine Eqv.trans (.productBeta (.let₂Beta p p
    (.let₂ (A := A) (B := B) (.var rfl)
      (.let₂ (A := A) (B := product A B) (.pair (.var rfl) (.var rfl))
        (.let₂ (A := A) (B := B) (.var rfl) (.br rfl (.pair (.var rfl) (.var rfl)))))))) ?_
  refine Eqv.trans (.productBeta (.let₂Beta a b
    (.let₂ (A := A) (B := product A B) (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))
      (.let₂ (A := A) (B := B) (.var rfl) (.br rfl (.pair (.var rfl) (.var rfl))))))) ?_
  refine Eqv.trans (.productBeta (.let₂Beta a p
    (.let₂ (A := A) (B := B) (.var rfl) (.br rfl (.pair (.var rfl) (.var rfl)))))) ?_
  exact .productBeta (.let₂Beta a b (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 0) rfl))))

theorem pairArrows_projections (A B : τ) :
    pairArrows (ofRegion (productFstBranches (Φ := Φ) A B))
      (ofRegion (productSndBranches A B)) = 𝟙 (obj (product A B)) := by
  unfold pairArrows diagonalArrow
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _ (seqBranches (whiskerRightRegion_typed (product A B) (productFstBranches A B))
      (whiskerLeftRegion_typed A (productSndBranches A B))),
    ofRegion_comp _ _ (repack_typed A B)]
  exact ((ofRegion_eq_iff _ _).mpr (repack_eqv A B)).trans (ofRegion_id (product A B))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductRepack
