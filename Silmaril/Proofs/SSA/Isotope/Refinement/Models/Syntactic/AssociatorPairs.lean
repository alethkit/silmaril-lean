module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.AssociatorReduction
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.PairReduction

/-! # Reassociation of pure product values -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- The inverse associator repacks three pure components, without copying or discarding them. -/
theorem assocInv_pair_equates {n : Nat} {Γ Γa Γbc Γb Γc : QCtx τ n}
    {a b c : Term Φ n} {A B C : τ}
    (s : Γ.Split Γa Γbc) (t : Γbc.Split Γb Γc)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ
      (.let₁ (.pair a (.pair b c)) (atIndex 0 (assocInvTerm : Term Φ 1)))
      (.pair (.pair a b) c) (product (product A B) C) := by
  have hqbc : quantity (product B C) ≤ Γbc.linearity := by
    rw [TypeQuantity.product_quantity]
    exact t.le_linearity (inf_le_left.trans hqb) (inf_le_right.trans hqc)
  have hqabc : quantity (product A (product B C)) ≤ Γ.linearity := by
    rw [TypeQuantity.product_quantity]
    exact s.le_linearity (inf_le_left.trans hqa) (inf_le_right.trans hqbc)
  have hp := HasType.pair s ha (HasType.pair t hb hc)
  have he₀ := pureBetaTyped (R := R) (QCtx.Split.zero_right Γ) hp
    (atZeroDeriv Γ (assocInvDeriv A B C (⊤ : ε))) hqabc
  have he₁ := purePairBeta (R := R) (QCtx.Split.zero_right Γ) s ha (.pair t hb hc)
    (assocInvAmbientBodyDeriv Γ.zero (QCtx.zero_discardable Γ) A B C (⊤ : ε)) hqa hqbc
  have hlin (D : τ) : Usage.effective (.used .linear) (quantity D) ≤
      Usage.effective (.used ⊤) (quantity D) := by
    change Quantity.linear ⊓ quantity D ≤ ⊤ ⊓ quantity D
    exact inf_le_inf bot_le le_rfl
  have hd := pairRightBindDeriv (pairRightBindDeriv ha B (.used ⊤) (hlin B))
    C (.used ⊤) (hlin C)
  have he₂ := purePairBeta (R := R) s.symm t hb hc hd.top hqb hqc
  apply he₀.trans
  change Equates F R Γ
    (.let₂ (.pair a (.pair b c)) (.let₂ (.bv 0) (.pair (.pair (.bv 3) (.bv 1)) (.bv 0)))) _ _
  apply he₁.trans
  convert he₂ using 1
  · change Tm.let₂ (.pair b c)
      (.pair (.pair (Tm.bsubst (Tm.upSub (Tm.upSub (Fin.cases (.pair b c) Tm.bv)))
        a.lift.lift.lift) (.bv 1)) (.bv 0)) =
      .let₂ (.pair b c) (.pair (.pair a.lift.lift (.bv 1)) (.bv 0))
    rw [Tm.bsubst_lift, Tm.bsubst_lift]
    change Tm.let₂ (.pair b c)
      (.pair (.pair (Tm.instantiate a.lift (.pair b c)).lift.lift (.bv 1)) (.bv 0)) = _
    rw [instantiate_lift]
  · change Tm.pair (.pair a b) c =
      .pair (.pair (Tm.instantiate (Tm.bsubst (Tm.upSub (Fin.cases b Tm.bv)) a.lift.lift) c)
        (Tm.instantiate b.lift c)) c
    rw [instantiate_lift]
    rw [Tm.bsubst_lift]
    change Tm.pair (.pair a b) c =
      .pair (.pair (Tm.instantiate (Tm.instantiate a.lift b).lift c) b) c
    rw [instantiate_lift, instantiate_lift]

/-- The associator has the expected action on three pure components. -/
theorem assoc_pair_equates {n : Nat} {Γ Γab Γa Γb Γc : QCtx τ n}
    {a b c : Term Φ n} {A B C : τ}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ
      (.let₁ (.pair (.pair a b) c) (atIndex 0 (assocTerm : Term Φ 1)))
      (.pair a (.pair b c)) (product A (product B C)) := by
  have hqab : quantity (product A B) ≤ Γab.linearity := by
    rw [TypeQuantity.product_quantity]
    exact t.le_linearity (inf_le_left.trans hqa) (inf_le_right.trans hqb)
  have hqabc : quantity (product (product A B) C) ≤ Γ.linearity := by
    rw [TypeQuantity.product_quantity]
    exact s.le_linearity (inf_le_left.trans hqab) (inf_le_right.trans hqc)
  have hp := HasType.pair s (HasType.pair t ha hb) hc
  have he₀ := pureBetaTyped (R := R) (QCtx.Split.zero_right Γ) hp
    (atZeroDeriv Γ (assocDeriv A B C (⊤ : ε))) hqabc
  have he₁ := purePairBeta (R := R) (QCtx.Split.zero_right Γ) s (.pair t ha hb) hc
    (assocAmbientBodyDeriv Γ.zero (QCtx.zero_discardable Γ) A B C (⊤ : ε)) hqab hqc
  have hlin (D : τ) : Usage.effective (.used .linear) (quantity D) ≤
      Usage.effective (.used ⊤) (quantity D) := by
    change Quantity.linear ⊓ quantity D ≤ ⊤ ⊓ quantity D
    exact inf_le_inf bot_le le_rfl
  have hd : HasType F ((Γc.snoc A).snoc B) (⊥ : ε)
      (.pair (.bv 1) (.pair (.bv 0) c.lift.lift)) (product A (product B C)) :=
    .pair (((QCtx.Split.zero_left Γc).snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
      ((zeroParameter Γc A (.used ⊤) (⊥ : ε) (hlin A)).rename Fin.succ (.insertZero _ B))
      (pairLeftBindDeriv (hc.rename Fin.succ (.insertZero Γc A)) B (.used ⊤) (hlin B))
  have he₂ := purePairBeta (R := R) s t ha hb hd.top hqa hqb
  apply he₀.trans
  change Equates F R Γ
    (.let₂ (.pair (.pair a b) c) (.let₂ (.bv 1) (.pair (.bv 1) (.pair (.bv 0) (.bv 2))))) _ _
  apply he₁.trans
  convert he₂ using 1
  · change Tm.let₂ (Tm.instantiate (Tm.pair a b).lift c)
      (.pair (.bv 1) (.pair (.bv 0) c.lift.lift)) = _
    rw [instantiate_lift]
  · change Tm.pair a (.pair b c) =
      .pair (Tm.instantiate a.lift b)
        (.pair b (Tm.instantiate (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) c.lift.lift) b))
    rw [instantiate_lift, Tm.bsubst_lift]
    change Tm.pair a (.pair b c) =
      .pair a (.pair b (Tm.instantiate (Tm.instantiate c.lift a).lift b))
    rw [instantiate_lift, instantiate_lift]

end Silmaril.Isotope.Refinement.Models.Syntactic
