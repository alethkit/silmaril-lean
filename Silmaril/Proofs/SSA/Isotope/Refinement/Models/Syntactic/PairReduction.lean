module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Binders

/-! # Eliminating pairs of pure values by native quantitative beta -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Product beta followed by its two guarded pure substitutions. Each
replacement supplies its intrinsic quantity from its own resource context. -/
theorem purePairBeta {n : Nat} {Γ Γab Γa Γb Γc : QCtx τ n}
    {a b : Term Φ n} {c : Term Φ (n + 2)} {A B C : τ}
    (outer : Γ.Split Γab Γc) (inner : Γab.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F ((Γc.snoc A).snoc B) (⊤ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity) :
    Equates (ε := ε) F R Γ (.let₂ (.pair a b) c)
      (Tm.instantiate (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) c) b) C := by
  obtain ⟨Γbc, wholeA, bc⟩ := outer.swapAssoc inner.symm
  obtain ⟨Γac, wholeB, ac⟩ := outer.swapAssoc inner
  have dseq : HasType F Γ (⊤ : ε) (.let₁ a (.let₁ b.lift c)) C :=
    .let₁ wholeA ha.top
      (.let₁ (bc.symm.snoc (.left (.used ⊤)))
        (hb.top.rename Fin.succ (.insertZero Γb A)) hc)
  have db := (((Substitution.Admissible.instantiate ac.symm ha hqa).up B).effectMono
    (show (⊥ : ε) ≤ ⊤ from bot_le)).typing hc
  have he₁ := pureBetaTyped (R := R) wholeA.symm ha
    (HasType.let₁ (bc.symm.snoc (.left (.used ⊤)))
      (hb.top.rename Fin.succ (.insertZero Γb A)) hc) hqa
  have he₂ := pureBetaTyped (R := R) wholeB.symm hb db hqb
  have heβ := Equates.ofAxiom (R := R)
    (.pairBeta outer inner ha.top hb.top hc)
    ⟨.let₂ outer.symm (.pair inner ha.top hb.top) hc⟩ ⟨dseq⟩
  apply heβ.trans
  apply he₁.trans
  change Equates F R Γ
    (.let₁ (Tm.instantiate b.lift a) (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) c)) _ C
  rw [instantiate_lift]
  exact he₂

end Silmaril.Isotope.Refinement.Models.Syntactic
