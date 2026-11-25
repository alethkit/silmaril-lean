module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Binders

/-! # Product elimination through a pure pairing context -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem pair_let₂_left {n : Nat} {Γ Γl Γm Γr Γc : QCtx τ n}
    {a c : Term Φ n} {b : Term Φ (n + 2)} {A B C D : τ}
    (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
    (ha : HasType F Γr (⊤ : ε) a (product A B))
    (hb : HasType F ((Γm.snoc A).snoc B) (⊤ : ε) b C)
    (hc : HasType F Γl (⊥ : ε) c D) :
    Equates (ε := ε) F R Γ (.pair (.let₂ a b) c)
      (.let₂ a (.pair b c.lift.lift)) (product C D) := by
  obtain ⟨Γmr, hsplit, hmr⟩ := outer.swapAssoc inner.symm
  have hlin : Usage.effective (.used .linear) (quantity C) ≤
      Usage.effective (.used ⊤) (quantity C) := by
    change Quantity.linear ⊓ quantity C ≤ ⊤ ⊓ quantity C
    exact inf_le_inf bot_le le_rfl
  have h₀ := pair_left_bind (R := R) hsplit (HasType.let₂ hmr ha hb) hc
  have h₁ := let_pair (R := R) outer inner ha hb
    (pairLeftBindDeriv hc C (.used ⊤) hlin).top
  have h₂ := pair_left_bind (R := R)
    ((inner.symm.snoc (.left (.used ⊤))).snoc (.left (.used ⊤))) hb
    ((hc.rename Fin.succ (.insertZero Γl A)).rename Fin.succ (.insertZero _ B))
  apply h₀.trans
  apply h₁.trans
  apply Equates.let₂ outer (Equates.refl ⟨ha⟩)
  convert h₂.symm using 1
  change Tm.let₁ b (Tm.rename (Tm.up Fin.succ)
    (Tm.rename (Tm.up Fin.succ) (.pair (.bv 0) c.lift))) =
    .let₁ b (.pair (.bv 0) c.lift.lift.lift)
  simp only [Tm.rename, Tm.rename_lift]
  rfl
  rfl

theorem pair_let₂_right {n : Nat} {Γ Γl Γm Γr Γc : QCtx τ n}
    {a c : Term Φ n} {b : Term Φ (n + 2)} {A B C D : τ}
    (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
    (ha : HasType F Γr (⊤ : ε) a (product A B))
    (hb : HasType F ((Γm.snoc A).snoc B) (⊤ : ε) b C)
    (hc : HasType F Γl (⊥ : ε) c D) :
    Equates (ε := ε) F R Γ (.pair c (.let₂ a b))
      (.let₂ a (.pair c.lift.lift b)) (product D C) := by
  obtain ⟨Γmr, hsplit, hmr⟩ := outer.swapAssoc inner.symm
  have hlin : Usage.effective (.used .linear) (quantity C) ≤
      Usage.effective (.used ⊤) (quantity C) := by
    change Quantity.linear ⊓ quantity C ≤ ⊤ ⊓ quantity C
    exact inf_le_inf bot_le le_rfl
  have h₀ := pair_right_bind (R := R) hsplit.symm hc (HasType.let₂ hmr ha hb)
  have h₁ := let_pair (R := R) outer inner ha hb
    (pairRightBindDeriv hc C (.used ⊤) hlin).top
  have h₂ := pair_right_bind (R := R)
    ((inner.snoc (.right (.used ⊤))).snoc (.right (.used ⊤)))
    ((hc.rename Fin.succ (.insertZero Γl A)).rename Fin.succ (.insertZero _ B)) hb
  apply h₀.trans
  apply h₁.trans
  apply Equates.let₂ outer (Equates.refl ⟨ha⟩)
  convert h₂.symm using 1
  change Tm.let₁ b (Tm.rename (Tm.up Fin.succ)
    (Tm.rename (Tm.up Fin.succ) (.pair c.lift (.bv 0)))) =
    .let₁ b (.pair c.lift.lift.lift (.bv 0))
  simp only [Tm.rename, Tm.rename_lift]
  rfl
  rfl

end Silmaril.Isotope.Refinement.Models.Syntactic
