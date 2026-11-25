module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IsoLaws

/-! # Involutivity of the native syntactic symmetry -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Destructuring the swapped parameter pair and swapping again returns the original pair. -/
theorem swapPair_equates (P A B : τ) :
    Equates (ε := ε) F R (pairContext P A B)
      (.let₂ (.pair (.bv 0) (.bv 1)) (.pair (.bv 0) (.bv 1)) : Term Φ 3)
      (.pair (.bv 1) (.bv 0)) (product A B) := by
  let Γ := pairContext P A B
  let Γa := pairLeftContext P A B
  let Γb := pairRightContext P A B
  let Γz := ((QCtx.nil.snoc P .zero).snoc A .zero).snoc B .zero
  have hz : Γz.Discardable := by
    intro i
    fin_cases i <;> exact le_rfl
  have hP : (QCtx.nil.snoc P .zero).Discardable := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact le_rfl
  have hPa : ((QCtx.nil.snoc P .zero).snoc A .zero).Discardable := by
    intro i
    fin_cases i <;> exact le_rfl
  have dq : HasType F Γ (⊤ : ε) (.pair (.bv 1) (.bv 0) : Term Φ 3) (product A B) :=
    parametersDeriv _ hP A B ⊤
  have hqa : quantity A ≤ Γa.linearity := by
    simp only [Γa, pairLeftContext, QCtx.linearity_snoc, Usage.linearity_zero,
      Usage.linearity_used, QCtx.linearity_nil, inf_top_eq]
    exact le_inf le_top (le_inf le_rfl le_top)
  have hqb : quantity B ≤ Γb.linearity := by
    simp only [Γb, pairRightContext, QCtx.linearity_snoc, Usage.linearity_zero,
      Usage.linearity_used, QCtx.linearity_nil, inf_top_eq]
    exact le_inf le_rfl (le_inf le_top le_top)
  have ha : Equates (ε := ε) F R Γ
      (.let₁ (.bv 1) (.pair (.bv 0) (.bv 1)) : Term Φ 3)
      (.pair (.bv 1) (.bv 0)) (product A B) :=
    pureBeta (pairSplit P A B) (leftParameter P A B (⊥ : ε))
      (swapParametersDeriv _ hPa B A (⊤ : ε)) hqa ⟨dq⟩
  have da : HasType F (Γa.snoc B) (⊤ : ε)
      (.let₁ (.bv 2) (.pair (.bv 0) (.bv 1)) : Term Φ 4) (product A B) := by
    let da := Classical.choice ha.1.wellTyped.1
    exact da.rename _ (.cons (.skip (.refl ((QCtx.nil.snoc P .zero).snoc A)) le_rfl) le_rfl)
  have hb : Equates (ε := ε) F R Γ
      (.let₁ (.bv 0) (.let₁ (.bv 2) (.pair (.bv 0) (.bv 1))) : Term Φ 3)
      (.let₁ (.bv 1) (.pair (.bv 0) (.bv 1))) (product A B) :=
    pureBeta (pairSplit P A B).symm (rightParameter P A B (⊥ : ε)) da hqb ha.1.wellTyped.1
  have hsplit : Γ.Split Γ Γz :=
    ((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc (.left (.used ⊤))
  have dp : HasType F Γ (⊤ : ε)
      (.let₂ (.pair (.bv 0) (.bv 1)) (.pair (.bv 0) (.bv 1)) : Term Φ 3) (product A B) :=
    .let₂ hsplit.symm
      (.pair (pairSplit P A B).symm (rightParameter _ _ _ _) (leftParameter _ _ _ _))
      (swapParametersDeriv Γz hz B A ⊤)
  exact (Equates.ofAxiom
    (.pairBeta hsplit (pairSplit P A B).symm
      (rightParameter P A B (⊤ : ε)) (leftParameter P A B ⊤)
      (swapParametersDeriv Γz hz B A ⊤)) ⟨dp⟩ hb.1.wellTyped.1).trans (hb.trans ha)

/-- The symmetry is its own inverse, by binding reassociation and product beta/eta. -/
theorem swap_swap_equates (A B : τ) :
    Equates (ε := ε) F R (input (product A B))
      (composeArrow (swapArrow (ε := ε) (Φ := Φ) (F := F) A B) (swapArrow B A)).val
      (.bv 0) (product A B) := by
  let P := product A B
  let Γ := pairContext P A B
  let Γz := ((QCtx.nil.snoc P .zero).snoc A .zero).snoc B .zero
  have hp : (QCtx.nil.snoc P .zero).Discardable := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact le_rfl
  have hz : Γz.Discardable := by intro i; fin_cases i <;> exact le_rfl
  have hsplit : Γ.Split Γ Γz :=
    ((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc (.left (.used ⊤))
  have hq : quantity (product B A) ≤ Γ.linearity := by
    simp only [TypeQuantity.product_quantity, Γ, pairContext, QCtx.linearity_snoc,
      Usage.linearity_zero, Usage.linearity_used, QCtx.linearity_nil, inf_top_eq]
    exact le_inf inf_le_left (le_inf inf_le_right le_top)
  have ds : HasType F (Γz.snoc (product B A)) (⊤ : ε)
      (.let₂ (.bv 0) (.pair (.bv 0) (.bv 1)) : Term Φ 4) P :=
    (swapDeriv (F := F) (Φ := Φ) B A (⊤ : ε)).rename _ ((QCtx.Weakening.empty Γz hz).up _)
  have hb : Equates (ε := ε) F R Γ
      (.let₁ (.pair (.bv 0) (.bv 1)) (.let₂ (.bv 0) (.pair (.bv 0) (.bv 1))) : Term Φ 3)
      (.pair (.bv 1) (.bv 0)) P :=
    (pureBeta hsplit (swapParametersDeriv _ hp A B (⊥ : ε)) ds hq
      (swapPair_equates (F := F) (Φ := Φ) (ε := ε) (R := R) P A B).1.wellTyped.1).trans
      (swapPair_equates P A B)
  let mid : Arrow (Φ := Φ) (ε := ε) F P P :=
    ⟨.let₂ (.bv 0) (.let₁ (.pair (.bv 0) (.bv 1)) (.let₂ (.bv 0) (.pair (.bv 0) (.bv 1)))), by
      obtain ⟨d⟩ := hb.1.wellTyped.1
      exact ⟨.let₂ (inputSplit P) (identityDeriv P ⊤) d⟩⟩
  apply Equates.trans (b := mid.val)
  · exact Equates.ofAxiom
      (.letLetPair (inputSplit P) (QCtx.Split.nil.snoc (.left .zero))
        (identityDeriv P (⊤ : ε)) (swapParametersDeriv _ hp A B ⊤)
        ((swapDeriv (F := F) (Φ := Φ) B A (⊤ : ε)).rename _
          ((QCtx.Weakening.insertZero QCtx.nil P).up _)))
      (composeArrow (swapArrow (ε := ε) (Φ := Φ) (F := F) A B) (swapArrow B A)).property mid.property
  · exact (Equates.let₂ (inputSplit P) (Equates.refl ⟨identityDeriv P (⊤ : ε)⟩) hb).trans
      (Equates.ofAxiom (.pairEta (identityDeriv P (⊤ : ε)))
        ⟨.let₂ (inputSplit P) (identityDeriv P ⊤) (parametersDeriv _ hp A B ⊤)⟩
        ⟨identityDeriv P ⊤⟩)

@[simp] theorem swap_swap (hR : R.RenamingClosed) (A B : τ) :
    compose (ε := ε) (F := F) (R := R) hR (swap A B) (swap B A) = identity (product A B) :=
  Quotient.sound (swap_swap_equates A B)

/-- The chosen syntactic symmetry is an actual categorical isomorphism. -/
def swapIso (hR : R.RenamingClosed) (A B : τ) :
    letI := category (ε := ε) F R hR
    CategoryTheory.Iso (product A B) (product B A) := by
  letI := category (ε := ε) F R hR
  exact ⟨swap A B, swap B A, swap_swap hR A B, swap_swap hR B A⟩

end Silmaril.Isotope.Refinement.Models.Syntactic
