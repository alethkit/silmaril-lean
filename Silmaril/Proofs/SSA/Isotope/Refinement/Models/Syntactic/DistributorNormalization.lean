module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.DistributivityAction
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseExtensionality

/-! # Normal forms for the canonical distributor and its inverse -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

def distributorTerm : Term Φ 1 :=
  descTerm (leftTerm (.inl (.bv 0))) (leftTerm (.inr (.bv 0)))

def distributorDeriv (cap : F.HasCase) (A B C : τ) (e : ε) :
    HasType F (input (coprod (product A B) (product A C))) e (distributorTerm : Term Φ 1)
      (product A (coprod B C)) :=
  descDeriv cap (leftDeriv A (inlDeriv cap B C e)) (leftDeriv A (inrDeriv cap B C e))

def distributorArrow (cap : F.HasCase) (A B C : τ) :
    Arrow (Φ := Φ) (ε := ε) F (coprod (product A B) (product A C)) (product A (coprod B C)) :=
  ⟨distributorTerm, ⟨distributorDeriv cap A B C ⊤⟩⟩

def distributor (cap : F.HasCase) (A B C : τ) :
    Hom (ε := ε) F R (coprod (product A B) (product A C)) (product A (coprod B C)) :=
  ofArrow (distributorArrow cap A B C)

theorem distributor_pure (cap : F.HasCase) (A B C : τ) :
    hasEffect (⊥ : ε) (distributor (R := R) cap A B C) :=
  ⟨distributorArrow cap A B C, rfl, ⟨distributorDeriv cap A B C ⊥⟩⟩

theorem distributor_eq_desc (hR : R.RenamingClosed) (cap : F.HasCase) (A B C : τ) :
    distributor (ε := ε) (R := R) cap A B C =
      desc hR cap (left hR A (inl cap B C)) (left hR A (inr cap B C)) := rfl

theorem pure_left_inl_action {n : Nat} {Γ Γa Γb : QCtx τ n}
    {a b : Term Φ n} {A B C : τ} (cap : F.HasCase) (s : Γ.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity) :
    Equates (ε := ε) F R Γ (action (.pair a b) (leftTerm (.inl (.bv 0))))
      (.pair a (.inl b)) (product A (coprod B C)) :=
  (pair_then_left s ha hb.top (inlDeriv cap B C (⊤ : ε)) hqa).trans
    (Equates.pair s (Equates.refl ⟨ha.top⟩) (pure_action_inl cap hb hqb))

theorem pure_left_inr_action {n : Nat} {Γ Γa Γc : QCtx τ n}
    {a c : Term Φ n} {A B C : τ} (cap : F.HasCase) (s : Γ.Split Γa Γc)
    (ha : HasType F Γa (⊥ : ε) a A) (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ (action (.pair a c) (leftTerm (.inr (.bv 0))))
      (.pair a (.inr c)) (product A (coprod B C)) :=
  (pair_then_left s ha hc.top (inrDeriv cap B C (⊤ : ε)) hqa).trans
    (Equates.pair s (Equates.refl ⟨ha.top⟩) (pure_action_inr cap hc hqc))

theorem left_inl_distributorInv_action {n : Nat} {Γ Γa Γb : QCtx τ n}
    {a b : Term Φ n} {A B C : τ} (cap : F.HasCase) (s : Γ.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair a b) (composeTerm (leftTerm (.inl (.bv 0))) distributorInvTerm))
      (.inl (.pair a b)) (coprod (product A B) (product A C)) :=
  (action_compose (HasType.pair s ha hb).top (leftDeriv A (inlDeriv cap B C (⊤ : ε)))
    (distributorInvDeriv cap A B C (⊤ : ε))).trans
    ((action_congr (pure_left_inl_action cap s ha hb hqa hqb)
      (distributorInvDeriv cap A B C (⊤ : ε))).trans
      (distributorInv_inl_action cap s ha hb hqa hqb))

theorem left_inr_distributorInv_action {n : Nat} {Γ Γa Γc : QCtx τ n}
    {a c : Term Φ n} {A B C : τ} (cap : F.HasCase) (s : Γ.Split Γa Γc)
    (ha : HasType F Γa (⊥ : ε) a A) (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair a c) (composeTerm (leftTerm (.inr (.bv 0))) distributorInvTerm))
      (.inr (.pair a c)) (coprod (product A B) (product A C)) :=
  (action_compose (HasType.pair s ha hc).top (leftDeriv A (inrDeriv cap B C (⊤ : ε)))
    (distributorInvDeriv cap A B C (⊤ : ε))).trans
    ((action_congr (pure_left_inr_action cap s ha hc hqa hqc)
      (distributorInvDeriv cap A B C (⊤ : ε))).trans
      (distributorInv_inr_action cap s ha hc hqa hqc))

theorem distributorInv_distributor_inl_action {n : Nat} {Γ Γa Γb : QCtx τ n}
    {a b : Term Φ n} {A B C : τ} (cap : F.HasCase) (s : Γ.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair a (.inl b)) (composeTerm distributorInvTerm distributorTerm))
      (.pair a (.inl b)) (product A (coprod B C)) :=
  (action_compose (HasType.pair s ha (HasType.inl cap hb)).top
    (distributorInvDeriv cap A B C (⊤ : ε)) (distributorDeriv cap A B C (⊤ : ε))).trans
    ((action_congr (distributorInv_inl_action cap s ha hb hqa hqb)
      (distributorDeriv cap A B C (⊤ : ε))).trans
      ((action_inl_desc cap (HasType.pair s ha hb).top
        (leftDeriv A (inlDeriv cap B C (⊤ : ε))) (leftDeriv A (inrDeriv cap B C (⊤ : ε)))).trans
        (pure_left_inl_action cap s ha hb hqa hqb)))

theorem distributorInv_distributor_inr_action {n : Nat} {Γ Γa Γc : QCtx τ n}
    {a c : Term Φ n} {A B C : τ} (cap : F.HasCase) (s : Γ.Split Γa Γc)
    (ha : HasType F Γa (⊥ : ε) a A) (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair a (.inr c)) (composeTerm distributorInvTerm distributorTerm))
      (.pair a (.inr c)) (product A (coprod B C)) :=
  (action_compose (HasType.pair s ha (HasType.inr cap hc)).top
    (distributorInvDeriv cap A B C (⊤ : ε)) (distributorDeriv cap A B C (⊤ : ε))).trans
    ((action_congr (distributorInv_inr_action cap s ha hc hqa hqc)
      (distributorDeriv cap A B C (⊤ : ε))).trans
      ((action_inr_desc cap (HasType.pair s ha hc).top
        (leftDeriv A (inlDeriv cap B C (⊤ : ε))) (leftDeriv A (inrDeriv cap B C (⊤ : ε)))).trans
        (pure_left_inr_action cap s ha hc hqa hqc)))

end Silmaril.Isotope.Refinement.Models.Syntactic
