module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Acts

/-! # Native action of pure structural arrows -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

namespace Acts

variable {n : Nat} {Γ Γa Γb Γc Γd Γab Γbc Γcd : QCtx τ n}
variable {a a' b b' c d : Term Φ n} {A A' B B' C D : τ}

theorem wellTyped {f : Hom (ε := ε) F R A B} (h : Acts Γ a f b) :
    WellTyped (ε := ε) F Γ b B := by
  obtain ⟨_, _, he⟩ := h
  exact he.1.wellTyped.2

theorem tensor (hR : R.RenamingClosed) (s : Γ.Split Γa Γb)
    (ha : HasType F Γa (⊤ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hqb : quantity B ≤ Γb.linearity)
    {f : Hom (ε := ε) F R A A'} {g : Hom (ε := ε) F R B B'}
    (h : Acts Γa a f a') (k : Acts Γb b g b') :
    Acts Γ (.pair a b) (Syntactic.compose hR (Syntactic.right hR f B) (Syntactic.left hR A' g)) (.pair a' b') := by
  obtain ⟨ha'⟩ := h.wellTyped
  exact (h.right hR s ha hb hqb).compose hR (HasType.pair s ha hb.top)
    (k.left hR s ha' hb.top)

theorem identity (ha : HasType F Γ (⊥ : ε) a A) (hq : quantity A ≤ Γ.linearity) :
    Acts Γ a (identity (F := F) (R := R) (ε := ε) A) a := by
  exact of_equates (r := identityArrow A)
    (pureBetaTyped (R := R) (QCtx.Split.zero_right Γ) ha
      (atZeroDeriv Γ (identityDeriv A (⊤ : ε))) hq)

theorem copy (ha : HasType F Γ (⊥ : ε) a A) (hc : Quantity.relevant ≤ quantity A)
    (hq : quantity A ≤ Γ.linearity) : Acts Γ a (copy (F := F) (R := R) (ε := ε) A hc) (.pair a a) :=
  of_equates (action_copy ha hc hq)

theorem discard (ha : HasType F Γ (⊥ : ε) a A) (hd : Quantity.affine ≤ quantity A)
    (hq : quantity A ≤ Γ.linearity) : Acts Γ a (discard (F := F) (R := R) (ε := ε) A hd) .unit := by
  exact of_equates (r := discardArrow A hd)
    (pureBetaTyped (R := R) (QCtx.Split.zero_right Γ) ha
      (atZeroDeriv Γ (discardDeriv A hd (⊤ : ε))) hq)

theorem leftUnitInv (ha : HasType F Γ (⊥ : ε) a A) (hq : quantity A ≤ Γ.linearity) :
    Acts Γ a (leftUnitInv (F := F) (R := R) (ε := ε) A) (.pair .unit a) := by
  exact of_equates (r := leftUnitInvArrow A)
    (pureBetaTyped (R := R) (QCtx.Split.zero_right Γ) ha
      (atZeroDeriv Γ (leftUnitInvDeriv A (⊤ : ε))) hq)

theorem rightUnitInv (ha : HasType F Γ (⊥ : ε) a A) (hq : quantity A ≤ Γ.linearity) :
    Acts Γ a (rightUnitInv (F := F) (R := R) (ε := ε) A) (.pair a .unit) := by
  exact of_equates (r := rightUnitInvArrow A)
    (pureBetaTyped (R := R) (QCtx.Split.zero_right Γ) ha
      (atZeroDeriv Γ (rightUnitInvDeriv A (⊤ : ε))) hq)

theorem swap (s : Γ.Split Γa Γb) (ha : HasType F Γa (⊥ : ε) a A)
    (hb : HasType F Γb (⊤ : ε) b B) (hqa : quantity A ≤ Γa.linearity) :
    Acts Γ (.pair a b) (swap (F := F) (R := R) (ε := ε) A B) (.pair b a) :=
  of_equates (pair_then_swap s ha hb hqa)

theorem assoc (s : Γ.Split Γab Γc) (t : Γab.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) :
    Acts Γ (.pair (.pair a b) c) (assoc (F := F) (R := R) (ε := ε) A B C) (.pair a (.pair b c)) :=
  of_equates (assoc_pair_equates s t ha hb hc hqa hqb hqc)

theorem assocInv (s : Γ.Split Γa Γbc) (t : Γbc.Split Γb Γc)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) :
    Acts Γ (.pair a (.pair b c)) (assocInv (F := F) (R := R) (ε := ε) A B C) (.pair (.pair a b) c) :=
  of_equates (assocInv_pair_equates s t ha hb hc hqa hqb hqc)

theorem middleSwap (s : Γ.Split Γab Γcd) (t : Γab.Split Γa Γb) (u : Γcd.Split Γc Γd)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C) (hd : HasType F Γd (⊥ : ε) d D)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity)
    (hqc : quantity C ≤ Γc.linearity) (hqd : quantity D ≤ Γd.linearity) :
    Acts Γ (.pair (.pair a b) (.pair c d)) (middleSwap (F := F) (R := R) (ε := ε) A B C D)
      (.pair (.pair a c) (.pair b d)) :=
  of_equates (middleSwap_action s t u ha hb hc hd hqa hqb hqc hqd)

end Acts
end Silmaril.Isotope.Refinement.Models.Syntactic
