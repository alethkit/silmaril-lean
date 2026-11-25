module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Associator
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Reduction
public import Silmaril.Raw.SSA.Isotope.Refinement.SubstitutionStructural

/-! # Pairing and sequencing in the native quantitative theory

Evaluation-order equations are derived from product eta/beta and guarded
linear beta. Commuting a component across a computation requires its purity.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless CategoryTheory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- The pair of the two newest variables uses every component exactly once. -/
def pairVariables {n : Nat} (Γ : QCtx τ n) (A B : τ) (e : ε) :
    HasType F ((Γ.zero.snoc A).snoc B) e
      (.pair (.bv 1) (.bv 0) : Term Φ (n + 2)) (product A B) := by
  have hs : Γ.zero.Split Γ.zero Γ.zero := fun _ => ⟨rfl, rfl, .left .zero⟩
  apply HasType.pair ((hs.snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
  · apply singleVariable ((Γ.zero.snoc A).snoc B .zero) 1 e rfl
    intro j hj
    refine Fin.cases (fun _ => rfl) (fun k hk => ?_) j hj
    exact Fin.cases (fun h => False.elim (h rfl)) (fun _ _ => rfl) k hk
  · apply singleVariable ((Γ.zero.snoc A .zero).snoc B) 0 e rfl
    intro j hj
    refine Fin.cases (fun h => False.elim (h rfl)) (fun k _ => ?_) j hj
    exact Fin.cases rfl (fun _ => rfl) k

/-- Typing of the sequential evaluation of two pair components. -/
def pairSequenceDeriv {n : Nat} {Γ Γl Γr : QCtx τ n} {e : ε}
    {a b : Term Φ n} {A B : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl e a A) (hb : HasType F Γr e b B) :
    HasType F Γ e (.let₁ a (.let₁ b.lift (.pair (.bv 1) (.bv 0)))) (product A B) :=
  .let₁ s.symm ha
    (.let₁ ((QCtx.Split.zero_left Γr).snoc (.left (.used ⊤)))
      (hb.rename Fin.succ (.insertZero Γr A)) (pairVariables Γr A B e))

/-- Pair evaluation is exactly left-to-right sequencing, derived by product
eta followed by product beta. -/
theorem pair_sequence {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {A B : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl (⊤ : ε) a A) (hb : HasType F Γr (⊤ : ε) b B) :
    Equates (ε := ε) F R Γ (.pair a b)
      (.let₁ a (.let₁ b.lift (.pair (.bv 1) (.bv 0)))) (product A B) := by
  have hp := HasType.pair s ha hb
  have hmid := HasType.let₂ (QCtx.Split.zero_left Γ) hp (pairVariables Γ A B (⊤ : ε))
  have heta := Equates.ofAxiom (R := R) (EquationAxiom.pairEta hp) ⟨hmid⟩ ⟨hp⟩
  have hbeta := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBeta (QCtx.Split.zero_right Γ) s ha hb (pairVariables Γ A B (⊤ : ε)))
    ⟨hmid⟩ ⟨pairSequenceDeriv s ha hb⟩
  exact heta.symm.trans hbeta

/-- A fresh parameter over an otherwise unused context. -/
def zeroParameter {n : Nat} (Γ : QCtx τ n) (A : τ) (q : Usage) (e : ε)
    (hq : Usage.effective (.used .linear) (quantity A) ≤ Usage.effective q (quantity A)) :
    HasType F (Γ.zero.snoc A q) e (.bv 0 : Term Φ (n + 1)) A := by
  apply HasType.var 0
  refine ⟨hq, ?_⟩
  intro i hi
  exact Fin.cases (fun h => False.elim (h rfl)) (fun _ _ => le_rfl) i hi

/-- The pure continuation pairing an existing value with its fresh parameter. -/
def pairRightBindDeriv {n : Nat} {Γ : QCtx τ n} {e : ε}
    {a : Term Φ n} {A : τ} (ha : HasType F Γ e a A) (B : τ) (q : Usage)
    (hq : Usage.effective (.used .linear) (quantity B) ≤ Usage.effective q (quantity B)) :
    HasType F (Γ.snoc B q) e (.pair a.lift (.bv 0)) (product A B) :=
  .pair ((QCtx.Split.zero_right Γ).snoc (.right q))
    (ha.rename Fin.succ (.insertZero Γ B)) (zeroParameter Γ B q e hq)

@[simp] theorem instantiate_lift {n : Nat} (a b : Term Φ n) :
    Tm.instantiate a.lift b = a := by
  simp only [Tm.instantiate, Tm.lift, Tm.bsubst_rename, Fin.cases_succ]
  exact Tm.bsubst_id a

/-- A pure left component can be retained while the right component executes.
Only the freshly bound result is substituted linearly. -/
theorem pair_right_bind {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {A B : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl (⊥ : ε) a A) (hb : HasType F Γr (⊤ : ε) b B) :
      Equates (ε := ε) F R Γ (.pair a b) (.let₁ b (.pair a.lift (.bv 0))) (product A B) := by
  have he : Tm.instantiate (.pair a.lift (.bv 0)) b = .pair a b := by
    change Tm.pair (Tm.instantiate a.lift b) b = Tm.pair a b
    rw [instantiate_lift]
  have hp : WellTyped (ε := ε) F Γ
      (Tm.instantiate (.pair a.lift (.bv 0)) b) (product A B) := by
    rw [he]
    exact ⟨.pair s ha.top hb⟩
  have h := linearBeta (R := R) s.symm hb
    (pairRightBindDeriv ha B (.used .linear) le_rfl)
    (pairRightBindDeriv ha B (.used ⊤) (by
      change Quantity.linear ⊓ quantity B ≤ ⊤ ⊓ quantity B
      exact inf_le_inf bot_le le_rfl))
    (EffectSystem.pure_commutes (⊤ : ε)).symm hp
  simpa only [he] using h.symm

/-- A pure left pair component is unaffected by sequencing on the right.
This is the local equation needed for left tensor functoriality. -/
theorem pair_let_right {n : Nat} {Γ Γa Γbc Γb Γc : QCtx τ n}
    {a b : Term Φ n} {c : Term Φ (n + 1)} {A B C : τ}
    (s : Γ.Split Γa Γbc) (t : Γbc.Split Γc Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊤ : ε) b B)
    (hc : HasType F (Γc.snoc B) (⊤ : ε) c C) :
    Equates (ε := ε) F R Γ (.pair a (.let₁ b c))
      (.let₁ b (.pair a.lift c)) (product A C) := by
  have hlift : Tm.rename Fin.succ a = a.lift := rfl
  have hp : (Tm.pair a.lift (.bv 0)).underBinder = .pair a.lift.lift (.bv 0) := by
    change Tm.pair (Tm.rename (Tm.up Fin.succ) a.lift) (.bv 0) = _
    rw [Tm.rename_lift]
    rfl
  obtain ⟨Γac, hs, ht⟩ := s.assoc t
  have hinit := pair_right_bind (R := R) s ha (HasType.let₁ t hb hc)
  have hq : Usage.effective (.used .linear) (quantity C) ≤
      Usage.effective (.used ⊤) (quantity C) := by
    change Quantity.linear ⊓ quantity C ≤ ⊤ ⊓ quantity C
    exact inf_le_inf bot_le le_rfl
  have hend := pair_right_bind (R := R) (ht.snoc (.right (.used ⊤)))
    (ha.rename Fin.succ (.insertZero Γa B)) hc
  have hmid : WellTyped (ε := ε) F Γ
      (.let₁ b (.let₁ c (Tm.pair a.lift (.bv 0)).underBinder)) (product A C) := by
    have h := HasType.let₁ hs hb (hend.1.wellTyped.2.some)
    simpa only [hp, hlift] using (show WellTyped (ε := ε) _ _ _ _ from ⟨h⟩)
  have hassoc := Equates.ofAxiom (R := R)
    (EquationAxiom.letLet hs ht hb hc (pairRightBindDeriv ha C (.used ⊤) hq).top)
    hinit.1.wellTyped.2 hmid
  have hcongr : Equates (ε := ε) F R Γ
      (.let₁ b (.pair a.lift c)) (.let₁ b (.let₁ c (Tm.pair a.lift (.bv 0)).underBinder))
      (product A C) := by
    constructor
    · apply Refines.let₁ hs (.refl ⟨hb⟩)
      simpa only [hp, hlift] using hend.1
    · apply Refines.let₁ hs (.refl ⟨hb⟩)
      simpa only [hp, hlift] using hend.2
  exact (hinit.trans hassoc).trans hcongr.symm

def pairLeftBindDeriv {n : Nat} {Γ : QCtx τ n} {e : ε}
    {b : Term Φ n} {B : τ} (hb : HasType F Γ e b B) (A : τ) (q : Usage)
    (hq : Usage.effective (.used .linear) (quantity A) ≤ Usage.effective q (quantity A)) :
    HasType F (Γ.snoc A q) e (.pair (.bv 0) b.lift) (product A B) :=
  .pair ((QCtx.Split.zero_left Γ).snoc (.left q))
    (zeroParameter Γ A q e hq) (hb.rename Fin.succ (.insertZero Γ A))

/-- A pure right component can be retained while the left component executes. -/
theorem pair_left_bind {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {A B : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl (⊤ : ε) a A) (hb : HasType F Γr (⊥ : ε) b B) :
    Equates (ε := ε) F R Γ (.pair a b) (.let₁ a (.pair (.bv 0) b.lift)) (product A B) := by
  have he : Tm.instantiate (.pair (.bv 0) b.lift) a = .pair a b := by
    change Tm.pair a (Tm.instantiate b.lift a) = Tm.pair a b
    rw [instantiate_lift]
  have hp : WellTyped (ε := ε) F Γ
      (Tm.instantiate (.pair (.bv 0) b.lift) a) (product A B) := by
    rw [he]
    exact ⟨.pair s ha hb.top⟩
  have h := linearBeta (R := R) s ha
    (pairLeftBindDeriv hb A (.used .linear) le_rfl)
    (pairLeftBindDeriv hb A (.used ⊤) (by
      change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
      exact inf_le_inf bot_le le_rfl))
    (EffectSystem.pure_commutes (⊤ : ε)).symm hp
  simpa only [he] using h.symm

/-- A pure right component is unaffected by sequencing on the left. -/
theorem pair_let_left {n : Nat} {Γ Γab Γc Γa Γb : QCtx τ n}
    {a c : Term Φ n} {b : Term Φ (n + 1)} {A B C : τ}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γb Γa)
    (ha : HasType F Γa (⊤ : ε) a A) (hb : HasType F (Γb.snoc A) (⊤ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C) :
    Equates (ε := ε) F R Γ (.pair (.let₁ a b) c)
      (.let₁ a (.pair b c.lift)) (product B C) := by
  have hlift : Tm.rename Fin.succ c = c.lift := rfl
  have hp : (Tm.pair (.bv 0) c.lift).underBinder = .pair (.bv 0) c.lift.lift := by
    change Tm.pair (.bv 0) (Tm.rename (Tm.up Fin.succ) c.lift) = _
    rw [Tm.rename_lift]
    rfl
  obtain ⟨Γcb, hs, ht⟩ := s.symm.assoc t
  have hinit := pair_left_bind (R := R) s (HasType.let₁ t ha hb) hc
  have hq : Usage.effective (.used .linear) (quantity B) ≤
      Usage.effective (.used ⊤) (quantity B) := by
    change Quantity.linear ⊓ quantity B ≤ ⊤ ⊓ quantity B
    exact inf_le_inf bot_le le_rfl
  have hend := pair_left_bind (R := R) (ht.symm.snoc (.left (.used ⊤))) hb
    (hc.rename Fin.succ (.insertZero Γc A))
  have hmid : WellTyped (ε := ε) F Γ
      (.let₁ a (.let₁ b (Tm.pair (.bv 0) c.lift).underBinder)) (product B C) := by
    have h := HasType.let₁ hs ha hend.1.wellTyped.2.some
    simpa only [hp, hlift] using (show WellTyped (ε := ε) _ _ _ _ from ⟨h⟩)
  have hassoc := Equates.ofAxiom (R := R)
    (EquationAxiom.letLet hs ht ha hb (pairLeftBindDeriv hc B (.used ⊤) hq).top)
    hinit.1.wellTyped.2 hmid
  have hcongr : Equates (ε := ε) F R Γ
      (.let₁ a (.pair b c.lift)) (.let₁ a (.let₁ b (Tm.pair (.bv 0) c.lift).underBinder))
      (product B C) := by
    constructor
    · apply Refines.let₁ hs (.refl ⟨ha⟩)
      simpa only [hp, hlift] using hend.1
    · apply Refines.let₁ hs (.refl ⟨ha⟩)
      simpa only [hp, hlift] using hend.2
  exact (hinit.trans hassoc).trans hcongr.symm

end Silmaril.Isotope.Refinement.Models.Syntactic
