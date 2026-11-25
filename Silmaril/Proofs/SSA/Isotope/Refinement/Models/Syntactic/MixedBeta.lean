module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Instantiation
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.PairReduction

/-! # Typed linear beta and mixed-effect product beta

A computation may replace a binder used linearly without a type-quantity
bound. Equational elimination still retains its effect-commutation premise.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment}

/-- A linear replacement commutes with the pure identity substitution on the
remaining context and requires no duplicability or discardability. -/
theorem Substitution.Admissible.instantiateLinear {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {A : τ} {e : ε} (split : Γ.Split Γl Γr)
    (ha : HasType F Γr e a A) :
    Substitution.Admissible F Γ e (Fin.cases a Tm.bv) (Γl.snoc A (.used .linear)) := by
  obtain ⟨Θ, hw, ⟨hs⟩⟩ := Substitution.Admissible.id (F := F) (Φ := Φ) Γl (⊥ : ε)
  refine ⟨Θ.snoc A (.used .linear), ?_,
    ⟨.cons split hs ha bot_le (EffectSystem.pure_commutes e) bot_le le_rfl⟩⟩
  convert QCtx.Weakening.cons hw (q := .used .linear) (q' := .used .linear) le_rfl using 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

namespace Models.Syntactic

variable {R : Relation τ Φ}

/-- Linear beta with the substituted target's formation derived from native
quantitative substitution. -/
theorem linearBetaTyped {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {b : Term Φ (n + 1)} {A B : τ} {e η : ε}
    (split : Γ.Split Γl Γr) (ha : HasType F Γl e a A)
    (hb : HasType F (Γr.snoc A (.used .linear)) η b B)
    (hbDefault : HasType F (Γr.snoc A) η b B)
    (commute : EffectSystem.commutes e η) :
    Equates (ε := ε) F R Γ (.let₁ a b) (Tm.instantiate b a) B :=
  linearBeta split ha hb hbDefault commute
    ⟨((Substitution.Admissible.instantiateLinear split.symm ha).effectMono
      (show e ≤ ⊤ from le_top)).typing hb.top⟩

/-- Product beta when the first component is pure and the second is used
linearly. The remaining continuation effect must commute with the latter. -/
theorem mixedPairBeta {n : Nat} {Γ Γab Γa Γb Γc : QCtx τ n}
    {a b : Term Φ n} {c : Term Φ (n + 2)} {A B C : τ} {e η : ε}
    (outer : Γ.Split Γab Γc) (inner : Γab.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb e b B)
    (hc : HasType F ((Γc.snoc A).snoc B (.used .linear)) η c C)
    (hcDefault : HasType F ((Γc.snoc A).snoc B) η c C)
    (hqa : quantity A ≤ Γa.linearity) (commute : EffectSystem.commutes e η) :
    Equates (ε := ε) F R Γ (.let₂ (.pair a b) c)
      (Tm.instantiate (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) c) b) C := by
  obtain ⟨Γbc, wholeA, bc⟩ := outer.swapAssoc inner.symm
  obtain ⟨Γac, wholeB, ac⟩ := outer.swapAssoc inner
  have dseq : HasType F Γ (⊤ : ε) (.let₁ a (.let₁ b.lift c)) C :=
    .let₁ wholeA ha.top
      (.let₁ (bc.symm.snoc (.left (.used ⊤)))
        (hb.top.rename Fin.succ (.insertZero Γb A)) hcDefault.top)
  have db := (((Substitution.Admissible.instantiate ac.symm ha hqa).up B (.used .linear)).effectMono
    (show (⊥ : ε) ≤ η from bot_le)).typing hc
  have dbDefault := (((Substitution.Admissible.instantiate ac.symm ha hqa).up B).effectMono
    (show (⊥ : ε) ≤ η from bot_le)).typing hcDefault
  have he₁ := pureBetaTyped (R := R) wholeA.symm ha
    (HasType.let₁ (bc.symm.snoc (.left (.used ⊤)))
      (hb.top.rename Fin.succ (.insertZero Γb A)) hcDefault.top) hqa
  have he₂ := linearBetaTyped (R := R) wholeB.symm hb db dbDefault commute
  have heβ := Equates.ofAxiom (R := R)
    (.pairBeta outer inner ha.top hb.top hcDefault.top)
    ⟨.let₂ outer.symm (.pair inner ha.top hb.top) hcDefault.top⟩ ⟨dseq⟩
  apply heβ.trans
  apply he₁.trans
  have he : Tm.instantiate (.let₁ b.lift c) a =
      .let₁ b (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) c) := by
    change Tm.let₁ (Tm.instantiate b.lift a) _ = _
    rw [instantiate_lift]
  rw [show Tm.rename Fin.succ b = b.lift from rfl, he]
  exact he₂

end Models.Syntactic
end Silmaril.Isotope.Refinement
