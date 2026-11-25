module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.HexagonAction

/-! # The middle-four interchange on pure product values -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Rebracket, exchange the two central components, and rebracket back. -/
def middleSwapTerm : Term Φ 1 :=
  composeTerm assocTerm
    (composeTerm (leftTerm assocInvTerm)
      (composeTerm (leftTerm (rightTerm swapTerm))
        (composeTerm (leftTerm assocTerm) assocInvTerm)))

def middleSwapDeriv (A B C D : τ) (e : ε) :
    HasType F (input (product (product A B) (product C D))) e (middleSwapTerm : Term Φ 1)
      (product (product A C) (product B D)) :=
  composeDeriv (assocDeriv A B (product C D) e)
    (composeDeriv (leftDeriv A (assocInvDeriv B C D e))
      (composeDeriv (leftDeriv A (rightDeriv D (swapDeriv B C e)))
        (composeDeriv (leftDeriv A (assocDeriv C B D e))
          (assocInvDeriv A C (product B D) e))))

def middleSwapArrow (A B C D : τ) :
    Arrow (Φ := Φ) (ε := ε) F (product (product A B) (product C D))
      (product (product A C) (product B D)) :=
  ⟨middleSwapTerm, ⟨middleSwapDeriv A B C D ⊤⟩⟩

def middleSwap (A B C D : τ) :
    Hom (ε := ε) F R (product (product A B) (product C D))
      (product (product A C) (product B D)) := ofArrow (middleSwapArrow A B C D)

/-- All four components retain their own resource contexts throughout the
structural interchange. No effect exchange principle is used. -/
theorem middleSwap_action {n : Nat} {Γ Γab Γcd Γa Γb Γc Γd : QCtx τ n}
    {a b c d : Term Φ n} {A B C D : τ}
    (s : Γ.Split Γab Γcd) (t : Γab.Split Γa Γb) (u : Γcd.Split Γc Γd)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C) (hd : HasType F Γd (⊥ : ε) d D)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) (hqd : quantity D ≤ Γd.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair (.pair a b) (.pair c d)) middleSwapTerm)
      (.pair (.pair a c) (.pair b d)) (product (product A C) (product B D)) := by
  obtain ⟨Γbcd, sa, sb⟩ := s.swapAssoc t.symm
  obtain ⟨Γbc, sd, sbc⟩ := sb.assoc u
  obtain ⟨Γbd, sc, sbd⟩ := sd.swapAssoc sbc
  have qcd : quantity (product C D) ≤ Γcd.linearity := by
    rw [TypeQuantity.product_quantity]
    exact u.le_linearity (inf_le_left.trans hqc) (inf_le_right.trans hqd)
  have qbd : quantity (product B D) ≤ Γbd.linearity := by
    rw [TypeQuantity.product_quantity]
    exact sbd.le_linearity (inf_le_left.trans hqb) (inf_le_right.trans hqd)
  have dp := HasType.pair s (.pair t ha hb) (.pair u hc hd)
  have dp₁ := HasType.pair sa.symm ha (.pair sb hb (.pair u hc hd))
  have dp₂ := HasType.pair sa.symm ha (.pair sd (.pair sbc hb hc) hd)
  have dp₃ := HasType.pair sa.symm ha (.pair sd (.pair sbc.symm hc hb) hd)
  have d₁ := leftDeriv (F := F) (Φ := Φ) A (assocInvDeriv B C D (⊤ : ε))
  have d₂ := leftDeriv (F := F) (Φ := Φ) A (rightDeriv D (swapDeriv B C (⊤ : ε)))
  have d₃ := leftDeriv (F := F) (Φ := Φ) A (assocDeriv C B D (⊤ : ε))
  have d₄ := assocInvDeriv (F := F) (Φ := Φ) A C (product B D) (⊤ : ε)
  have rest₃ := composeDeriv d₃ d₄
  have rest₂ := composeDeriv d₂ rest₃
  have rest₁ := composeDeriv d₁ rest₂
  have h₀ := action_compose (R := R) dp.top (assocDeriv A B (product C D) (⊤ : ε)) rest₁
  have h₁ := action_congr (assoc_pair_equates (R := R) s t ha hb (.pair u hc hd) hqa hqb qcd) rest₁
  have h₂ := action_compose (R := R) dp₁.top d₁ rest₂
  have hi₁ := (pair_then_left_any (R := R) sa.symm ha.top (HasType.pair sb hb (.pair u hc hd)).top
    (assocInvDeriv B C D (⊤ : ε))).trans
    (Equates.pair sa.symm (Equates.refl ⟨ha.top⟩)
      (assocInv_pair_equates (R := R) sb u hb hc hd hqb hqc hqd))
  have h₃ := action_congr hi₁ rest₂
  have h₄ := action_compose (R := R) dp₂.top d₂ rest₃
  have hi₂inner := (pair_then_right (R := R) sd (HasType.pair sbc hb hc).top hd
    (swapDeriv B C (⊤ : ε)) hqd).trans
    (Equates.pair sd (pair_then_swap (R := R) sbc hb hc.top hqb) (Equates.refl ⟨hd.top⟩))
  have hi₂ := (pair_then_left_any (R := R) sa.symm ha.top (HasType.pair sd (.pair sbc hb hc) hd).top
    (rightDeriv D (swapDeriv B C (⊤ : ε)))).trans
    (Equates.pair sa.symm (Equates.refl ⟨ha.top⟩) hi₂inner)
  have h₅ := action_congr hi₂ rest₃
  have h₆ := action_compose (R := R) dp₃.top d₃ d₄
  have hi₃ := (pair_then_left_any (R := R) sa.symm ha.top
    (HasType.pair sd (.pair sbc.symm hc hb) hd).top (assocDeriv C B D (⊤ : ε))).trans
    (Equates.pair sa.symm (Equates.refl ⟨ha.top⟩)
      (assoc_pair_equates (R := R) sd sbc.symm hc hb hd hqc hqb hqd))
  have h₇ := action_congr hi₃ d₄
  have h₈ := assocInv_pair_equates (R := R) sa.symm sc.symm ha hc (.pair sbd hb hd) hqa hqc qbd
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans h₈)))))))

end Silmaril.Isotope.Refinement.Models.Syntactic
