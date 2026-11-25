module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CoproductAction

/-! # Case tests inside a pure product context -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

def pairInlBindDeriv {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A : τ} {e : ε}
    (cap : F.HasCase) (ha : HasType F Γ e a A) (B C : τ) :
    HasType F (Γ.snoc B) e (.pair a.lift (.inl (.bv 0))) (product A (coprod B C)) :=
  .pair ((QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)))
    (ha.rename Fin.succ (.insertZero Γ B))
    (.inl cap (zeroParameter Γ B (.used ⊤) e (by
      change Quantity.linear ⊓ quantity B ≤ ⊤ ⊓ quantity B
      exact inf_le_inf bot_le le_rfl)))

def pairInrBindDeriv {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A : τ} {e : ε}
    (cap : F.HasCase) (ha : HasType F Γ e a A) (B C : τ) :
    HasType F (Γ.snoc C) e (.pair a.lift (.inr (.bv 0))) (product A (coprod B C)) :=
  .pair ((QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)))
    (ha.rename Fin.succ (.insertZero Γ C))
    (.inr cap (zeroParameter Γ C (.used ⊤) e (by
      change Quantity.linear ⊓ quantity C ≤ ⊤ ⊓ quantity C
      exact inf_le_inf bot_le le_rfl)))

/-- Equality after both injections suffices to compare an action on a product with a sum. -/
theorem action_pair_case_ext {n : Nat} {Γ Γa Γs : QCtx τ n}
    {a s : Term Φ n} {f g : Term Φ 1} {A B C D : τ}
    (cap : F.HasCase) (split : Γ.Split Γa Γs)
    (ha : HasType F Γa (⊥ : ε) a A) (hs : HasType F Γs (⊤ : ε) s (coprod B C))
    (hf : HasType F (input (product A (coprod B C))) (⊤ : ε) f D)
    (hg : HasType F (input (product A (coprod B C))) (⊤ : ε) g D)
    (hl : Equates (ε := ε) F R (Γa.snoc B)
      (action (.pair a.lift (.inl (.bv 0))) f) (action (.pair a.lift (.inl (.bv 0))) g) D)
    (hr : Equates (ε := ε) F R (Γa.snoc C)
      (action (.pair a.lift (.inr (.bv 0))) f) (action (.pair a.lift (.inr (.bv 0))) g) D) :
    Equates (ε := ε) F R Γ (action (.pair a s) f) (action (.pair a s) g) D := by
  have hlin (E : τ) : Usage.effective (.used .linear) (quantity E) ≤
      Usage.effective (.used ⊤) (quantity E) := by
    change Quantity.linear ⊓ quantity E ≤ ⊤ ⊓ quantity E
    exact inf_le_inf bot_le le_rfl
  have dl := HasType.inl (B := C) cap (zeroParameter (Φ := Φ) Γs B (.used ⊤) (⊤ : ε) (hlin B))
  have dr := HasType.inr (A := B) cap (zeroParameter (Φ := Φ) Γs C (.used ⊤) (⊤ : ε) (hlin C))
  have heta := Equates.ofAxiom (R := R) (.caseEta cap hs)
    ⟨.case cap (QCtx.Split.zero_left Γs) hs dl dr⟩ ⟨hs⟩
  have hpair := Equates.pair split (Equates.refl ⟨ha.top⟩) heta.symm
  have hmove := pair_case_right (R := R) cap split.symm (QCtx.Split.zero_left Γs) hs dl dr ha
  have hn (k : Term Φ 1)
      (hk : HasType F (input (product A (coprod B C))) (⊤ : ε) k D) :
      Equates (ε := ε) F R Γ (action (.pair a s) k)
        (.case s (action (.pair a.lift (.inl (.bv 0))) k)
          (action (.pair a.lift (.inr (.bv 0))) k)) D :=
    (action_congr hpair hk).trans ((action_congr hmove hk).trans
      (action_case cap split hs (pairInlBindDeriv cap ha B C).top
        (pairInrBindDeriv cap ha B C).top hk))
  exact (hn f hf).trans ((Equates.case cap split (Equates.refl ⟨hs⟩) hl hr).trans (hn g hg).symm)

end Silmaril.Isotope.Refinement.Models.Syntactic
