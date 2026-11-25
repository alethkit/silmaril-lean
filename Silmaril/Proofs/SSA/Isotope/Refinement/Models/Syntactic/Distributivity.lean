module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.DistributorNormalization
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Extensionality
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Coproducts

/-! # Native distributivity as an actual categorical isomorphism -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem leftParameter_quantity (P A B : τ) : quantity A ≤ (pairLeftContext P A B).linearity := by
  apply QCtx.le_linearity_iff.mpr
  intro i
  fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top

theorem rightParameter_quantity (P A B : τ) : quantity B ≤ (pairRightContext P A B).linearity := by
  apply QCtx.le_linearity_iff.mpr
  intro i
  fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top

theorem left_inl_distributorInv_equates (cap : F.HasCase) (A B C : τ) :
    Equates (ε := ε) F R (input (product A B))
      (composeTerm (leftTerm (.inl (.bv 0))) distributorInvTerm) (.inl (.bv 0))
      (coprod (product A B) (product A C)) := by
  let P := product A B
  let s := pairSplit P A B
  have da := leftParameter (F := F) (Φ := Φ) P A B (⊥ : ε)
  have db := rightParameter (F := F) (Φ := Φ) P A B (⊥ : ε)
  have qa := leftParameter_quantity P A B
  have qb := rightParameter_quantity P A B
  have q : quantity (product A B) ≤ (pairContext P A B).linearity := by
    rw [TypeQuantity.product_quantity]
    exact s.le_linearity (inf_le_left.trans qa) (inf_le_right.trans qb)
  apply pair_ext
    (composeDeriv (leftDeriv A (inlDeriv cap B C (⊤ : ε))) (distributorInvDeriv cap A B C (⊤ : ε)))
    (inlDeriv cap (product A B) (product A C) (⊤ : ε))
  exact (left_inl_distributorInv_action cap s da db qa qb).trans
    (pure_action_inl cap (HasType.pair s da db) q).symm

theorem left_inr_distributorInv_equates (cap : F.HasCase) (A B C : τ) :
    Equates (ε := ε) F R (input (product A C))
      (composeTerm (leftTerm (.inr (.bv 0))) distributorInvTerm) (.inr (.bv 0))
      (coprod (product A B) (product A C)) := by
  let P := product A C
  let s := pairSplit P A C
  have da := leftParameter (F := F) (Φ := Φ) P A C (⊥ : ε)
  have dc := rightParameter (F := F) (Φ := Φ) P A C (⊥ : ε)
  have qa := leftParameter_quantity P A C
  have qc := rightParameter_quantity P A C
  have q : quantity (product A C) ≤ (pairContext P A C).linearity := by
    rw [TypeQuantity.product_quantity]
    exact s.le_linearity (inf_le_left.trans qa) (inf_le_right.trans qc)
  apply pair_ext
    (composeDeriv (leftDeriv A (inrDeriv cap B C (⊤ : ε))) (distributorInvDeriv cap A B C (⊤ : ε)))
    (inrDeriv cap (product A B) (product A C) (⊤ : ε))
  exact (left_inr_distributorInv_action cap s da dc qa qc).trans
    (pure_action_inr cap (HasType.pair s da dc) q).symm

theorem distributorInv_distributor_equates (cap : F.HasCase) (A B C : τ) :
    Equates (ε := ε) F R (input (product A (coprod B C)))
      (composeTerm distributorInvTerm distributorTerm) (.bv 0) (product A (coprod B C)) := by
  let P := product A (coprod B C)
  let Γa := pairLeftContext P A (coprod B C)
  have da := leftParameter (F := F) (Φ := Φ) P A (coprod B C) (⊥ : ε)
  have ds := rightParameter (F := F) (Φ := Φ) P A (coprod B C) (⊤ : ε)
  have qa : quantity A ≤ Γa.linearity := leftParameter_quantity P A (coprod B C)
  have hlin (E : τ) : Usage.effective (.used .linear) (quantity E) ≤
      Usage.effective (.used ⊤) (quantity E) := by
    change Quantity.linear ⊓ quantity E ≤ ⊤ ⊓ quantity E
    exact inf_le_inf bot_le le_rfl
  have qlift (E : τ) : quantity A ≤ (Γa.snoc E .zero).linearity := by
    rw [QCtx.linearity_snoc, Usage.linearity_zero]
    exact le_inf le_top qa
  have qparam (E : τ) : quantity E ≤ (Γa.zero.snoc E).linearity := by
    rw [QCtx.linearity_snoc, Usage.linearity_used, QCtx.zero_linearity]
    exact le_inf (le_inf le_rfl le_top) le_top
  have df := composeDeriv (distributorInvDeriv (Φ := Φ) cap A B C (⊤ : ε))
    (distributorDeriv cap A B C (⊤ : ε))
  apply pair_ext df (identityDeriv P (⊤ : ε))
  apply action_pair_case_ext cap (pairSplit P A (coprod B C)) da ds df (identityDeriv P (⊤ : ε))
  · let s := (QCtx.Split.zero_right Γa).snoc (A := B) (.right (.used ⊤))
    have da' := da.rename Fin.succ (.insertZero Γa B)
    have db := zeroParameter (F := F) (Φ := Φ) Γa B (.used ⊤) (⊥ : ε) (hlin B)
    have dp := HasType.pair s da' (HasType.inl (B := C) cap db)
    have q : quantity P ≤ (Γa.snoc B).linearity := by
      rw [TypeQuantity.product_quantity, TypeQuantity.coproduct_quantity]
      exact s.le_linearity (inf_le_left.trans (qlift B))
        ((inf_le_right.trans inf_le_left).trans (qparam B))
    have hid := pureBetaTyped (R := R) (QCtx.Split.zero_right (Γa.snoc B)) dp
      (atZeroDeriv (Γa.snoc B) (identityDeriv P (⊤ : ε))) q
    exact (distributorInv_distributor_inl_action cap s da' db (qlift B) (qparam B)).trans hid.symm
  · let s := (QCtx.Split.zero_right Γa).snoc (A := C) (.right (.used ⊤))
    have da' := da.rename Fin.succ (.insertZero Γa C)
    have dc := zeroParameter (F := F) (Φ := Φ) Γa C (.used ⊤) (⊥ : ε) (hlin C)
    have dp := HasType.pair s da' (HasType.inr (A := B) cap dc)
    have q : quantity P ≤ (Γa.snoc C).linearity := by
      rw [TypeQuantity.product_quantity, TypeQuantity.coproduct_quantity]
      exact s.le_linearity (inf_le_left.trans (qlift C))
        ((inf_le_right.trans inf_le_right).trans (qparam C))
    have hid := pureBetaTyped (R := R) (QCtx.Split.zero_right (Γa.snoc C)) dp
      (atZeroDeriv (Γa.snoc C) (identityDeriv P (⊤ : ε))) q
    exact (distributorInv_distributor_inr_action cap s da' dc (qlift C) (qparam C)).trans hid.symm

@[simp] theorem left_inl_distributorInv (hR : R.RenamingClosed) (cap : F.HasCase) (A B C : τ) :
    compose (ε := ε) (R := R) hR (left hR A (inl cap B C)) (distributorInv cap A B C) =
      inl cap (product A B) (product A C) :=
  Quotient.sound (left_inl_distributorInv_equates cap A B C)

@[simp] theorem left_inr_distributorInv (hR : R.RenamingClosed) (cap : F.HasCase) (A B C : τ) :
    compose (ε := ε) (R := R) hR (left hR A (inr cap B C)) (distributorInv cap A B C) =
      inr cap (product A B) (product A C) :=
  Quotient.sound (left_inr_distributorInv_equates cap A B C)

@[simp] theorem distributor_distributorInv (hR : R.RenamingClosed) (cap : F.HasCase) (A B C : τ) :
    compose (ε := ε) (R := R) hR (distributor cap A B C) (distributorInv cap A B C) =
      identity (coprod (product A B) (product A C)) := by
  rw [distributor_eq_desc hR, desc_compose, left_inl_distributorInv, left_inr_distributorInv, desc_inl_inr]

@[simp] theorem distributorInv_distributor (hR : R.RenamingClosed) (cap : F.HasCase) (A B C : τ) :
    compose (ε := ε) (R := R) hR (distributorInv cap A B C) (distributor cap A B C) =
      identity (product A (coprod B C)) :=
  Quotient.sound (distributorInv_distributor_equates cap A B C)

/-- The canonical distributor is invertible, by equations of the native calculus. -/
def distributorIso (hR : R.RenamingClosed) (cap : F.HasCase) (A B C : τ) :
    letI := category (ε := ε) F R hR
    CategoryTheory.Iso (coprod (product A B) (product A C)) (product A (coprod B C)) := by
  letI := category (ε := ε) F R hR
  exact ⟨distributor cap A B C, distributorInv cap A B C,
    distributor_distributorInv hR cap A B C, distributorInv_distributor hR cap A B C⟩

end Silmaril.Isotope.Refinement.Models.Syntactic
