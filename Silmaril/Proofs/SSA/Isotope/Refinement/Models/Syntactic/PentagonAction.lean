module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Extensionality

/-! # Componentwise normalization of the associativity pentagon -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem pentagon_action_short {n : Nat} {Γ Γabc Γab Γa Γb Γc Γd : QCtx τ n}
    {a b c d : Term Φ n} {A B C D : τ}
    (s : Γ.Split Γabc Γd) (t : Γabc.Split Γab Γc) (u : Γab.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C) (hd : HasType F Γd (⊥ : ε) d D)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) (hqd : quantity D ≤ Γd.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair (.pair (.pair a b) c) d) (composeTerm assocTerm assocTerm))
      (.pair a (.pair b (.pair c d))) (product A (product B (product C D))) := by
  obtain ⟨Γcd, sab, cd⟩ := s.swapAssoc t.symm
  have hqab : quantity (product A B) ≤ Γab.linearity := by
    rw [TypeQuantity.product_quantity]
    exact u.le_linearity (inf_le_left.trans hqa) (inf_le_right.trans hqb)
  have hqcd : quantity (product C D) ≤ Γcd.linearity := by
    rw [TypeQuantity.product_quantity]
    exact cd.le_linearity (inf_le_left.trans hqc) (inf_le_right.trans hqd)
  have dp := HasType.pair s (.pair t (.pair u ha hb) hc) hd
  have he₀ := action_compose (R := R) dp.top (assocDeriv (product A B) C D (⊤ : ε))
    (assocDeriv A B (product C D) (⊤ : ε))
  have he₁ := action_congr
    (assoc_pair_equates (R := R) s t (HasType.pair u ha hb) hc hd hqab hqc hqd)
    (assocDeriv A B (product C D) (⊤ : ε))
  have he₂ := assoc_pair_equates (R := R) sab.symm u ha hb (HasType.pair cd hc hd) hqa hqb hqcd
  exact he₀.trans (he₁.trans he₂)

theorem pentagon_action_long {n : Nat} {Γ Γabc Γab Γa Γb Γc Γd : QCtx τ n}
    {a b c d : Term Φ n} {A B C D : τ}
    (s : Γ.Split Γabc Γd) (t : Γabc.Split Γab Γc) (u : Γab.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C) (hd : HasType F Γd (⊥ : ε) d D)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) (hqd : quantity D ≤ Γd.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair (.pair (.pair a b) c) d)
        (composeTerm (rightTerm assocTerm) (composeTerm assocTerm (leftTerm assocTerm))))
      (.pair a (.pair b (.pair c d))) (product A (product B (product C D))) := by
  obtain ⟨Γbc, ta, bc⟩ := t.swapAssoc u.symm
  obtain ⟨Γbcd, sa, bcd⟩ := s.swapAssoc ta
  have hqbc : quantity (product B C) ≤ Γbc.linearity := by
    rw [TypeQuantity.product_quantity]
    exact bc.le_linearity (inf_le_left.trans hqb) (inf_le_right.trans hqc)
  have dp := HasType.pair s (.pair t (.pair u ha hb) hc) hd
  have dq := HasType.pair s (.pair ta.symm ha (.pair bc hb hc)) hd
  have dα₀ := assocDeriv (F := F) (Φ := Φ) A B C (⊤ : ε)
  have dα₁ := assocDeriv (F := F) (Φ := Φ) A (product B C) D (⊤ : ε)
  have dα₂ := assocDeriv (F := F) (Φ := Φ) B C D (⊤ : ε)
  have he₀ := action_compose (R := R) dp.top (rightDeriv D dα₀) (composeDeriv dα₁ (leftDeriv A dα₂))
  have hright := (pair_then_right (R := R) s (HasType.pair t (.pair u ha hb) hc).top hd dα₀ hqd).trans
    (Equates.pair s (assoc_pair_equates (R := R) t u ha hb hc hqa hqb hqc) (Equates.refl ⟨hd.top⟩))
  have he₁ := action_congr hright (composeDeriv dα₁ (leftDeriv A dα₂))
  have he₂ := action_compose (R := R) dq.top dα₁ (leftDeriv A dα₂)
  have he₃ := action_congr
    (assoc_pair_equates (R := R) s ta.symm ha (HasType.pair bc hb hc) hd hqa hqbc hqd)
    (leftDeriv A dα₂)
  have he₄ := (pair_then_left (R := R) sa.symm ha (HasType.pair bcd (.pair bc hb hc) hd).top dα₂ hqa).trans
    (Equates.pair sa.symm (Equates.refl ⟨ha.top⟩)
      (assoc_pair_equates (R := R) bcd bc hb hc hd hqb hqc hqd))
  exact he₀.trans (he₁.trans (he₂.trans (he₃.trans he₄)))

end Silmaril.Isotope.Refinement.Models.Syntactic
