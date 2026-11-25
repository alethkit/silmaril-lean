module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Exchange
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Binders

/-! # Moving ordered pairing through product elimination -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Pairing evaluates its left product elimination before its right component.
Moving the latter into the continuation preserves arbitrary effects. -/
theorem pair_let₂_left_any {n : Nat} {Γ Γab Γc Γa Γb : QCtx τ n}
    {a c : Term Φ n} {b : Term Φ (n + 2)} {A B C D : τ}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γb Γa)
    (ha : HasType F Γa (⊤ : ε) a (product A B))
    (hb : HasType F ((Γb.snoc A).snoc B) (⊤ : ε) b D)
    (hc : HasType F Γc (⊤ : ε) c C) :
    Equates (ε := ε) F R Γ (.pair (.let₂ a b) c)
      (.let₂ a (.pair b c.lift.lift)) (product D C) := by
  obtain ⟨Γcb, hs, ht⟩ := s.symm.assoc t
  have hinit := pair_left_bind_any (R := R) s (HasType.let₂ t ha hb) hc
  have hq : Usage.effective (.used .linear) (quantity D) ≤
      Usage.effective (.used ⊤) (quantity D) := by
    change Quantity.linear ⊓ quantity D ≤ ⊤ ⊓ quantity D
    exact inf_le_inf bot_le le_rfl
  have hend := pair_left_bind_any (R := R)
    ((ht.symm.snoc (.left (.used ⊤))).snoc (.left (.used ⊤))) hb
    ((hc.rename Fin.succ (.insertZero Γc A)).rename Fin.succ (.insertZero _ B))
  have hassoc := let_pair (R := R) hs ht ha hb (pairLeftBindDeriv hc D (.used ⊤) hq)
  have hp : (Tm.pair (.bv 0) c.lift).underBinder.underBinder =
      .pair (.bv 0) c.lift.lift.lift := by
    change Tm.pair (.bv 0) (Tm.rename (Tm.up Fin.succ) (Tm.rename (Tm.up Fin.succ) c.lift)) = _
    rw [Tm.rename_lift, Tm.rename_lift]
    rfl
  have hcongr := Equates.let₂ hs (Equates.refl (R := R) ⟨ha⟩) hend
  simp only [show Tm.rename Fin.succ c = c.lift from rfl,
    show Tm.rename Fin.succ c.lift = c.lift.lift from rfl] at hcongr
  exact (hinit.trans (by simpa only [hp] using hassoc)).trans hcongr.symm

end Silmaril.Isotope.Refinement.Models.Syntactic
