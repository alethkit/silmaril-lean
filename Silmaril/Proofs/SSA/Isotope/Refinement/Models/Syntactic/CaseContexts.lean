module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseReduction

/-! # Case analysis through sequential and pure pairing contexts -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem action_case {n : Nat} {Γ Γl Γr : QCtx τ n} {a : Term Φ n}
    {l r : Term Φ (n + 1)} {f : Term Φ 1} {A B C D : τ}
    (cap : F.HasCase) (split : Γ.Split Γl Γr)
    (ha : HasType F Γr (⊤ : ε) a (coprod A B))
    (hl : HasType F (Γl.snoc A) (⊤ : ε) l C)
    (hr : HasType F (Γl.snoc B) (⊤ : ε) r C)
    (hf : HasType F (input C) (⊤ : ε) f D) :
    Equates (ε := ε) F R Γ (action (.case a l r) f)
      (.case a (action l f) (action r f)) D := by
  have h := let_case (R := R) cap (QCtx.Split.zero_right Γ) split ha hl hr (atZeroDeriv Γ hf)
  simpa only [action, underBinder_atIndex_zero] using h

theorem pair_case_right {n : Nat} {Γ Γbranches Γarg Γcase Γpure : QCtx τ n}
    {a c : Term Φ n} {l r : Term Φ (n + 1)} {A B C D : τ}
    (cap : F.HasCase) (outer : Γ.Split Γcase Γpure)
    (inner : Γcase.Split Γbranches Γarg)
    (ha : HasType F Γarg (⊤ : ε) a (coprod A B))
    (hl : HasType F (Γbranches.snoc A) (⊤ : ε) l C)
    (hr : HasType F (Γbranches.snoc B) (⊤ : ε) r C)
    (hc : HasType F Γpure (⊥ : ε) c D) :
    Equates (ε := ε) F R Γ (.pair c (.case a l r))
      (.case a (.pair c.lift l) (.pair c.lift r)) (product D C) := by
  obtain ⟨Γrest, whole, rest⟩ := outer.swapAssoc inner
  have hlin : Usage.effective (.used .linear) (quantity C) ≤
      Usage.effective (.used ⊤) (quantity C) := by
    change Quantity.linear ⊓ quantity C ≤ ⊤ ⊓ quantity C
    exact inf_le_inf bot_le le_rfl
  have h₀ := pair_right_bind (R := R) outer.symm hc (.case cap inner ha hl hr)
  have h₁ := let_case (R := R) cap outer inner ha hl hr
    (pairRightBindDeriv hc C (.used ⊤) hlin).top
  have hL := pair_right_bind (R := R) (rest.symm.snoc (.right (.used ⊤)))
    (hc.rename Fin.succ (.insertZero Γpure A)) hl
  have hR := pair_right_bind (R := R) (rest.symm.snoc (.right (.used ⊤)))
    (hc.rename Fin.succ (.insertZero Γpure B)) hr
  have he : (Tm.pair c.lift (.bv 0)).underBinder = .pair c.lift.lift (.bv 0) := by
    change Tm.pair (Tm.rename (Tm.up Fin.succ) c.lift) (.bv 0) = _
    rw [Tm.rename_lift]
    rfl
  apply h₀.trans
  apply h₁.trans
  rw [he]
  exact Equates.case cap whole (Equates.refl ⟨ha⟩) hL.symm hR.symm

theorem pair_case_left {n : Nat} {Γ Γbranches Γarg Γcase Γpure : QCtx τ n}
    {a c : Term Φ n} {l r : Term Φ (n + 1)} {A B C D : τ}
    (cap : F.HasCase) (outer : Γ.Split Γcase Γpure)
    (inner : Γcase.Split Γbranches Γarg)
    (ha : HasType F Γarg (⊤ : ε) a (coprod A B))
    (hl : HasType F (Γbranches.snoc A) (⊤ : ε) l C)
    (hr : HasType F (Γbranches.snoc B) (⊤ : ε) r C)
    (hc : HasType F Γpure (⊥ : ε) c D) :
    Equates (ε := ε) F R Γ (.pair (.case a l r) c)
      (.case a (.pair l c.lift) (.pair r c.lift)) (product C D) := by
  obtain ⟨Γrest, whole, rest⟩ := outer.swapAssoc inner
  have hlin : Usage.effective (.used .linear) (quantity C) ≤
      Usage.effective (.used ⊤) (quantity C) := by
    change Quantity.linear ⊓ quantity C ≤ ⊤ ⊓ quantity C
    exact inf_le_inf bot_le le_rfl
  have h₀ := pair_left_bind (R := R) outer (.case cap inner ha hl hr) hc
  have h₁ := let_case (R := R) cap outer inner ha hl hr
    (pairLeftBindDeriv hc C (.used ⊤) hlin).top
  have hL := pair_left_bind (R := R) (rest.snoc (.left (.used ⊤))) hl
    (hc.rename Fin.succ (.insertZero Γpure A))
  have hR := pair_left_bind (R := R) (rest.snoc (.left (.used ⊤))) hr
    (hc.rename Fin.succ (.insertZero Γpure B))
  have he : (Tm.pair (.bv 0) c.lift).underBinder = .pair (.bv 0) c.lift.lift := by
    change Tm.pair (.bv 0) (Tm.rename (Tm.up Fin.succ) c.lift) = _
    rw [Tm.rename_lift]
    rfl
  apply h₀.trans
  apply h₁.trans
  rw [he]
  exact Equates.case cap whole (Equates.refl ⟨ha⟩) hL.symm hR.symm

end Silmaril.Isotope.Refinement.Models.Syntactic
