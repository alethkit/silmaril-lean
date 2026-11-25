module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.DistributivitySyntax

/-! # The inverse distributor on injected pure components -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem distributorInv_inl_action {n : Nat} {Γ Γa Γb : QCtx τ n}
    {a b : Term Φ n} {A B C : τ} (cap : F.HasCase) (s : Γ.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity) :
    Equates (ε := ε) F R Γ (action (.pair a (.inl b)) distributorInvTerm)
      (.inl (.pair a b)) (coprod (product A B) (product A C)) := by
  have hqs : quantity (coprod B C) ≤ Γb.linearity := by
    rw [TypeQuantity.coproduct_quantity]
    exact inf_le_left.trans hqb
  have hqp : quantity (product A (coprod B C)) ≤ Γ.linearity := by
    rw [TypeQuantity.product_quantity]
    exact s.le_linearity (inf_le_left.trans hqa) (inf_le_right.trans hqs)
  have hp := HasType.pair s ha (HasType.inl (B := C) cap hb)
  have he₀ := pureBetaTyped (R := R) (QCtx.Split.zero_right Γ) hp
    (atZeroDeriv Γ (distributorInvDeriv cap A B C (⊤ : ε))) hqp
  have he₁ := purePairBeta (R := R) (QCtx.Split.zero_right Γ) s ha (.inl cap hb)
    (distributorInvBodyDeriv cap Γ.zero (QCtx.zero_discardable Γ) A B C (⊤ : ε)) hqa hqs
  have hlin (D : τ) : Usage.effective (.used .linear) (quantity D) ≤
      Usage.effective (.used ⊤) (quantity D) := by
    change Quantity.linear ⊓ quantity D ≤ ⊤ ⊓ quantity D
    exact inf_le_inf bot_le le_rfl
  have he₂ := pureCaseBetaL (R := R) cap s hb
    (HasType.inl cap (pairRightBindDeriv ha B (.used ⊤) (hlin B))).top
    (HasType.inr cap (pairRightBindDeriv ha C (.used ⊤) (hlin C))).top hqb
  apply he₀.trans
  change Equates F R Γ (.let₂ (.pair a (.inl b)) distributorInvBody) _ _
  apply he₁.trans
  convert he₂ using 1
  · change Tm.case (.inl b)
      (.inl (.pair (Tm.bsubst (Tm.upSub (Fin.cases (.inl b) Tm.bv)) a.lift.lift) (.bv 0)))
      (.inr (.pair (Tm.bsubst (Tm.upSub (Fin.cases (.inl b) Tm.bv)) a.lift.lift) (.bv 0))) = _
    rw [Tm.bsubst_lift]
    change Tm.case (.inl b)
      (.inl (.pair (Tm.instantiate a.lift (.inl b)).lift (.bv 0)))
      (.inr (.pair (Tm.instantiate a.lift (.inl b)).lift (.bv 0))) = _
    rw [instantiate_lift]
  · change Tm.inl (.pair a b) = .inl (.pair (Tm.instantiate a.lift b) b)
    rw [instantiate_lift]

theorem distributorInv_inr_action {n : Nat} {Γ Γa Γc : QCtx τ n}
    {a c : Term Φ n} {A B C : τ} (cap : F.HasCase) (s : Γ.Split Γa Γc)
    (ha : HasType F Γa (⊥ : ε) a A) (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ (action (.pair a (.inr c)) distributorInvTerm)
      (.inr (.pair a c)) (coprod (product A B) (product A C)) := by
  have hqs : quantity (coprod B C) ≤ Γc.linearity := by
    rw [TypeQuantity.coproduct_quantity]
    exact inf_le_right.trans hqc
  have hqp : quantity (product A (coprod B C)) ≤ Γ.linearity := by
    rw [TypeQuantity.product_quantity]
    exact s.le_linearity (inf_le_left.trans hqa) (inf_le_right.trans hqs)
  have hp := HasType.pair s ha (HasType.inr (A := B) cap hc)
  have he₀ := pureBetaTyped (R := R) (QCtx.Split.zero_right Γ) hp
    (atZeroDeriv Γ (distributorInvDeriv cap A B C (⊤ : ε))) hqp
  have he₁ := purePairBeta (R := R) (QCtx.Split.zero_right Γ) s ha (.inr cap hc)
    (distributorInvBodyDeriv cap Γ.zero (QCtx.zero_discardable Γ) A B C (⊤ : ε)) hqa hqs
  have hlin (D : τ) : Usage.effective (.used .linear) (quantity D) ≤
      Usage.effective (.used ⊤) (quantity D) := by
    change Quantity.linear ⊓ quantity D ≤ ⊤ ⊓ quantity D
    exact inf_le_inf bot_le le_rfl
  have he₂ := pureCaseBetaR (R := R) cap s hc
    (HasType.inl cap (pairRightBindDeriv ha B (.used ⊤) (hlin B))).top
    (HasType.inr cap (pairRightBindDeriv ha C (.used ⊤) (hlin C))).top hqc
  apply he₀.trans
  change Equates F R Γ (.let₂ (.pair a (.inr c)) distributorInvBody) _ _
  apply he₁.trans
  convert he₂ using 1
  · change Tm.case (.inr c)
      (.inl (.pair (Tm.bsubst (Tm.upSub (Fin.cases (.inr c) Tm.bv)) a.lift.lift) (.bv 0)))
      (.inr (.pair (Tm.bsubst (Tm.upSub (Fin.cases (.inr c) Tm.bv)) a.lift.lift) (.bv 0))) = _
    rw [Tm.bsubst_lift]
    change Tm.case (.inr c)
      (.inl (.pair (Tm.instantiate a.lift (.inr c)).lift (.bv 0)))
      (.inr (.pair (Tm.instantiate a.lift (.inr c)).lift (.bv 0))) = _
    rw [instantiate_lift]
  · change Tm.inr (.pair a c) = .inr (.pair (Tm.instantiate a.lift c) c)
    rw [instantiate_lift]

end Silmaril.Isotope.Refinement.Models.Syntactic
