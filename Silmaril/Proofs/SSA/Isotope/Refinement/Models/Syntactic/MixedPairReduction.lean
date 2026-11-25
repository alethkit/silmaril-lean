module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.MixedBeta

/-! # Product beta with an effectful first component -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Product beta when the first component is used linearly and the second
is pure. The continuation must commute with the first computation. -/
theorem mixedPairBeta_right {n : Nat} {Γ Γab Γa Γb Γc : QCtx τ n}
    {a b : Term Φ n} {c : Term Φ (n + 2)} {A B C : τ} {e η : ε}
    (outer : Γ.Split Γab Γc) (inner : Γab.Split Γa Γb)
    (ha : HasType F Γa e a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F ((Γc.snoc A (.used .linear)).snoc B) η c C)
    (hcDefault : HasType F ((Γc.snoc A).snoc B) η c C)
    (hqb : quantity B ≤ Γb.linearity) (commute : EffectSystem.commutes e η) :
    Equates (ε := ε) F R Γ (.let₂ (.pair a b) c)
      (Tm.instantiate (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) c) b) C := by
  obtain ⟨Γbc, wholeA, bc⟩ := outer.swapAssoc inner.symm
  obtain ⟨Γac, wholeB, ac⟩ := outer.swapAssoc inner
  have ds := HasType.let₁ (bc.symm.snoc (.left (.used .linear)))
    ((hb.effectMono (show (⊥ : ε) ≤ η from bot_le)).rename Fin.succ (.insertZero Γb A)) hc
  have dsDefault := HasType.let₁ (bc.symm.snoc (.left (.used ⊤)))
    ((hb.effectMono (show (⊥ : ε) ≤ η from bot_le)).rename Fin.succ (.insertZero Γb A)) hcDefault
  have db := (((Substitution.Admissible.instantiateLinear ac.symm ha).up B).effectMono
    (show e ≤ ⊤ from le_top)).typing hc.top
  have he₁ := linearBetaTyped (R := R) wholeA.symm ha ds dsDefault commute
  have he₂ := pureBetaTyped (R := R) wholeB.symm hb db hqb
  have heβ := Equates.ofAxiom (R := R)
    (.pairBeta outer inner ha.top hb.top hcDefault.top)
    ⟨.let₂ outer.symm (.pair inner ha.top hb.top) hcDefault.top⟩
    ⟨.let₁ wholeA ha.top dsDefault.top⟩
  apply heβ.trans
  apply he₁.trans
  have he : Tm.instantiate (.let₁ b.lift c) a =
      .let₁ b (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) c) := by
    change Tm.let₁ (Tm.instantiate b.lift a) _ = _
    rw [instantiate_lift]
  rw [show Tm.rename Fin.succ b = b.lift from rfl, he]
  exact he₂

end Silmaril.Isotope.Refinement.Models.Syntactic
