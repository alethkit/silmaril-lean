module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Extensionality
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Naturality

/-! # Componentwise normalization of the braiding hexagons -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- The raw symmetry representative does not depend on the component types. -/
def swapTerm : Term Φ 1 := .let₂ (.bv 0) (.pair (.bv 0) (.bv 1))

theorem hexagon_forward_action_left {n : Nat} {Γ Γab Γa Γb Γc : QCtx τ n}
    {a b c : Term Φ n} {A B C : τ}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair (.pair a b) c) (composeTerm assocTerm (composeTerm swapTerm assocTerm)))
      (.pair b (.pair c a)) (product B (product C A)) := by
  obtain ⟨Γbc, sa, bc⟩ := s.swapAssoc t.symm
  have dp := HasType.pair s (.pair t ha hb) hc
  have dq := HasType.pair sa.symm ha (.pair bc hb hc)
  have ds := swapDeriv (F := F) (Φ := Φ) A (product B C) (⊤ : ε)
  have dr := assocDeriv (F := F) (Φ := Φ) B C A (⊤ : ε)
  have he₀ := action_compose (R := R) dp.top (assocDeriv A B C (⊤ : ε)) (composeDeriv ds dr)
  have he₁ := action_congr (assoc_pair_equates (R := R) s t ha hb hc hqa hqb hqc)
    (composeDeriv ds dr)
  have he₂ := action_compose (R := R) dq.top ds dr
  have he₃ := action_congr (pair_then_swap (R := R) sa.symm ha (HasType.pair bc hb hc).top hqa) dr
  have he₄ := assoc_pair_equates (R := R) sa bc hb hc ha hqb hqc hqa
  exact he₀.trans (he₁.trans (he₂.trans (he₃.trans he₄)))

theorem hexagon_forward_action_right {n : Nat} {Γ Γab Γa Γb Γc : QCtx τ n}
    {a b c : Term Φ n} {A B C : τ}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair (.pair a b) c)
        (composeTerm (rightTerm swapTerm) (composeTerm assocTerm (leftTerm swapTerm))))
      (.pair b (.pair c a)) (product B (product C A)) := by
  obtain ⟨Γac, sb, ac⟩ := s.swapAssoc t
  have dp := HasType.pair s (.pair t ha hb) hc
  have dq := HasType.pair s (.pair t.symm hb ha) hc
  have dr := HasType.pair sb.symm hb (.pair ac ha hc)
  have ds := swapDeriv (F := F) (Φ := Φ) A B (⊤ : ε)
  have dt := swapDeriv (F := F) (Φ := Φ) A C (⊤ : ε)
  have dα := assocDeriv (F := F) (Φ := Φ) B A C (⊤ : ε)
  have he₀ := action_compose (R := R) dp.top (rightDeriv C ds) (composeDeriv dα (leftDeriv B dt))
  have hright := (pair_then_right (R := R) s (HasType.pair t ha hb).top hc ds hqc).trans
    (Equates.pair s (pair_then_swap (R := R) t ha hb.top hqa) (Equates.refl ⟨hc.top⟩))
  have he₁ := action_congr hright (composeDeriv dα (leftDeriv B dt))
  have he₂ := action_compose (R := R) dq.top dα (leftDeriv B dt)
  have he₃ := action_congr (assoc_pair_equates (R := R) s t.symm hb ha hc hqb hqa hqc)
    (leftDeriv B dt)
  have he₄ := (pair_then_left (R := R) sb.symm hb (HasType.pair ac ha hc).top dt hqb).trans
    (Equates.pair sb.symm (Equates.refl ⟨hb.top⟩) (pair_then_swap (R := R) ac ha hc.top hqa))
  exact he₀.trans (he₁.trans (he₂.trans (he₃.trans he₄)))

theorem hexagon_reverse_action_left {n : Nat} {Γ Γa Γbc Γb Γc : QCtx τ n}
    {a b c : Term Φ n} {A B C : τ}
    (s : Γ.Split Γa Γbc) (t : Γbc.Split Γb Γc)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair a (.pair b c))
        (composeTerm assocInvTerm (composeTerm swapTerm assocInvTerm)))
      (.pair (.pair c a) b) (product (product C A) B) := by
  obtain ⟨Γab, sc, ab⟩ := s.assoc t
  have hqab : quantity (product A B) ≤ Γab.linearity := by
    rw [TypeQuantity.product_quantity]
    exact ab.le_linearity (inf_le_left.trans hqa) (inf_le_right.trans hqb)
  have dp := HasType.pair s ha (.pair t hb hc)
  have dq := HasType.pair sc (.pair ab ha hb) hc
  have ds := swapDeriv (F := F) (Φ := Φ) (product A B) C (⊤ : ε)
  have dr := assocInvDeriv (F := F) (Φ := Φ) C A B (⊤ : ε)
  have he₀ := action_compose (R := R) dp.top (assocInvDeriv A B C (⊤ : ε)) (composeDeriv ds dr)
  have he₁ := action_congr (assocInv_pair_equates (R := R) s t ha hb hc hqa hqb hqc)
    (composeDeriv ds dr)
  have he₂ := action_compose (R := R) dq.top ds dr
  have he₃ := action_congr (pair_then_swap (R := R) sc (HasType.pair ab ha hb) hc.top hqab) dr
  have he₄ := assocInv_pair_equates (R := R) sc.symm ab hc ha hb hqc hqa hqb
  exact he₀.trans (he₁.trans (he₂.trans (he₃.trans he₄)))

theorem hexagon_reverse_action_right {n : Nat} {Γ Γa Γbc Γb Γc : QCtx τ n}
    {a b c : Term Φ n} {A B C : τ}
    (s : Γ.Split Γa Γbc) (t : Γbc.Split Γb Γc)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair a (.pair b c))
        (composeTerm (leftTerm swapTerm) (composeTerm assocInvTerm (rightTerm swapTerm))))
      (.pair (.pair c a) b) (product (product C A) B) := by
  obtain ⟨Γac, sb, ac⟩ := s.assoc t.symm
  have dp := HasType.pair s ha (.pair t hb hc)
  have dq := HasType.pair s ha (.pair t.symm hc hb)
  have ds := swapDeriv (F := F) (Φ := Φ) B C (⊤ : ε)
  have dt := swapDeriv (F := F) (Φ := Φ) A C (⊤ : ε)
  have dα := assocInvDeriv (F := F) (Φ := Φ) A C B (⊤ : ε)
  have he₀ := action_compose (R := R) dp.top (leftDeriv A ds) (composeDeriv dα (rightDeriv B dt))
  have hleft := (pair_then_left (R := R) s ha (HasType.pair t hb hc).top ds hqa).trans
    (Equates.pair s (Equates.refl ⟨ha.top⟩) (pair_then_swap (R := R) t hb hc.top hqb))
  have he₁ := action_congr hleft (composeDeriv dα (rightDeriv B dt))
  have he₂ := action_compose (R := R) dq.top dα (rightDeriv B dt)
  have he₃ := action_congr (assocInv_pair_equates (R := R) s t.symm ha hc hb hqa hqc hqb)
    (rightDeriv B dt)
  have he₄ := (pair_then_right (R := R) sb (HasType.pair ac ha hc).top hb dt hqb).trans
    (Equates.pair sb (pair_then_swap (R := R) ac ha hc.top hqa) (Equates.refl ⟨hb.top⟩))
  exact he₀.trans (he₁.trans (he₂.trans (he₃.trans he₄)))

end Silmaril.Isotope.Refinement.Models.Syntactic
