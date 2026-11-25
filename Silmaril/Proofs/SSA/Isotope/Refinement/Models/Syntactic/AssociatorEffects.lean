module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.AssociatorNaturality
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.MixedPairReduction
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.ProductContexts

/-! # Reassociation with effectful product components -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Reassociation consumes the product it destructures exactly once. -/
def assocBodyLeftUsageDeriv {n : Nat} (Γ : QCtx τ n) (A B C : τ) (q : Usage) (e : ε)
    (hq : Usage.effective (.used .linear) (quantity (product A B)) ≤
      Usage.effective q (quantity (product A B))) :
    HasType F ((Γ.zero.snoc (product A B) q).snoc C) e
      (assocBody (Φ := Φ)) (product A (product B C)) := by
  have hz : Γ.zero.Split Γ.zero Γ.zero := fun _ => ⟨rfl, rfl, .left .zero⟩
  have htop : Usage.effective (.used .linear) (quantity C) ≤
      Usage.effective (.used ⊤) (quantity C) := by
    change Quantity.linear ⊓ quantity C ≤ ⊤ ⊓ quantity C
    exact inf_le_inf bot_le le_rfl
  exact .let₂ ((hz.snoc (.right q)).snoc (.left (.used ⊤)))
    ((zeroParameter (F := F) (Φ := Φ) Γ (product A B) q e hq).rename Fin.succ (.insertZero _ C))
    (assocBodyUsageDeriv Γ A B C (.used ⊤) e htop).let₂View.body

/-- Reassociation preserves an effectful left product while retaining a pure
right component. The retained component carries its written quantity bound. -/
theorem pair_then_assoc_right {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {A B C : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl (⊤ : ε) a (product A B)) (hb : HasType F Γr (⊥ : ε) b C)
    (hq : quantity C ≤ Γr.linearity) :
    Equates (ε := ε) F R Γ
      (.let₁ (.pair a b) (atIndex 0 (assocTerm (Φ := Φ))))
      (.let₂ a (.pair (.bv 1) (.pair (.bv 0) b.lift.lift))) (product A (product B C)) := by
  have hc := assocBodyLeftUsageDeriv (F := F) (Φ := Φ) Γ A B C (.used .linear) (⊥ : ε) le_rfl
  have hqd : Usage.effective (.used .linear) (quantity (product A B)) ≤
      Usage.effective (.used ⊤) (quantity (product A B)) := by
    change Quantity.linear ⊓ quantity (product A B) ≤ ⊤ ⊓ quantity (product A B)
    exact inf_le_inf bot_le le_rfl
  have hd := assocBodyLeftUsageDeriv (F := F) (Φ := Φ) Γ A B C (.used ⊤) (⊥ : ε) hqd
  have hp := HasType.pair s ha hb.top
  have hbind := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBind (QCtx.Split.zero_left Γ) hp hd.top)
    ⟨.let₂ (QCtx.Split.zero_left Γ) hp hd.top⟩
    (show WellTyped (ε := ε) F Γ
      (.let₁ (.pair a b) (atIndex 0 (assocTerm (Φ := Φ)))) (product A (product B C)) from
      ⟨.let₁ (QCtx.Split.zero_left Γ) hp (atZeroDeriv Γ (assocDeriv A B C (⊤ : ε)))⟩)
  have hβ := mixedPairBeta_right (R := R) (QCtx.Split.zero_right Γ) s ha hb hc hd hq
    (EffectSystem.pure_commutes (⊤ : ε)).symm
  have he : Tm.instantiate (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv))
      (assocBody (n := n) (Φ := Φ))) b =
      .let₂ a (.pair (.bv 1) (.pair (.bv 0) b.lift.lift)) := by
    change Tm.let₂ (Tm.instantiate a.lift b) (.pair (.bv 1) (.pair (.bv 0) b.lift.lift)) = _
    rw [instantiate_lift]
  have hbind' : Equates (ε := ε) F R Γ (.let₂ (.pair a b) assocBody)
      (.let₁ (.pair a b) (atIndex 0 (assocTerm (Φ := Φ)))) (product A (product B C)) := hbind
  exact hbind'.symm.trans (by simpa only [he] using hβ)

/-- The associator preserves the evaluation of an effectful first leaf. -/
theorem assoc_pair_first {n : Nat} {Γ Γab Γa Γb Γc : QCtx τ n}
    {a b c : Term Φ n} {A B C : τ}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γa Γb)
    (ha : HasType F Γa (⊤ : ε) a A) (hb : HasType F Γb (⊥ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C)
    (hqb : quantity B ≤ Γb.linearity) (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ
      (.let₁ (.pair (.pair a b) c) (atIndex 0 (assocTerm (Φ := Φ))))
      (.pair a (.pair b c)) (product A (product B C)) := by
  have hlin (D : τ) : Usage.effective (.used .linear) (quantity D) ≤
      Usage.effective (.used ⊤) (quantity D) := by
    change Quantity.linear ⊓ quantity D ≤ ⊤ ⊓ quantity D
    exact inf_le_inf bot_le le_rfl
  have hd (q : Usage) (hq : Usage.effective (.used .linear) (quantity A) ≤
      Usage.effective q (quantity A)) :
      HasType F ((Γc.snoc A q).snoc B) (⊥ : ε)
        (.pair (.bv 1) (.pair (.bv 0) c.lift.lift)) (product A (product B C)) :=
    .pair (((QCtx.Split.zero_left Γc).snoc (.left q)).snoc (.right (.used ⊤)))
      ((zeroParameter Γc A q (⊥ : ε) hq).rename Fin.succ (.insertZero _ B))
      (pairLeftBindDeriv (hc.rename Fin.succ (.insertZero Γc A)) B (.used ⊤) (hlin B))
  have h₁ := pair_then_assoc_right (R := R) s (HasType.pair t ha hb.top) hc hqc
  have h₂ := mixedPairBeta_right (R := R) s t ha hb (hd (.used .linear) le_rfl)
    (hd (.used ⊤) (hlin A)) hqb (EffectSystem.pure_commutes (⊤ : ε)).symm
  apply h₁.trans
  convert h₂ using 1
  change Tm.pair a (.pair b c) =
    .pair (Tm.instantiate a.lift b)
      (.pair b (Tm.instantiate (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) c.lift.lift) b))
  rw [instantiate_lift, Tm.bsubst_lift]
  change Tm.pair a (.pair b c) =
    .pair a (.pair b (Tm.instantiate (Tm.instantiate c.lift a).lift b))
  rw [instantiate_lift, instantiate_lift]

end Silmaril.Isotope.Refinement.Models.Syntactic
