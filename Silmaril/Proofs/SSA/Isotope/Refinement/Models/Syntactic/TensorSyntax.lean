module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Pairing

/-! # Typed representatives and local equations for tensor application -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless CategoryTheory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Interpret a singleton computation at one specified variable. -/
def atIndex {n : Nat} (i : Fin n) (a : Term Φ 1) : Term Φ n := Tm.rename (fun _ => i) a

@[simp] theorem rename_atIndex {n m : Nat} (ρ : Fin n → Fin m) (i : Fin n) (a : Term Φ 1) :
    Tm.rename ρ (atIndex i a) = atIndex (ρ i) a := Tm.rename_comp _ _ _

@[simp] theorem atIndex_zero (a : Term Φ 1) : atIndex 0 a = a := by
  unfold atIndex
  calc
    Tm.rename (fun _ => 0) a = Tm.rename (fun i => i) a :=
      Tm.rename_congr (fun i => (Fin.eq_zero i).symm) a
    _ = a := Tm.rename_id a

theorem continuation_atIndex (a : Term Φ 1) : continuation a = atIndex 0 a := by
  apply Tm.rename_congr
  intro i
  have hi := Fin.eq_zero i
  subst i
  rfl

theorem onRight_atIndex (a : Term Φ 1) : onRight a = atIndex 0 a := by
  apply Tm.rename_congr
  intro i
  have hi := Fin.eq_zero i
  subst i
  rfl

theorem onLeft_atIndex (a : Term Φ 1) : onLeft a = atIndex 1 a := by
  apply Tm.rename_congr
  intro i
  have hi := Fin.eq_zero i
  subst i
  rfl

theorem atIndex_compose {n : Nat} (i : Fin n) (a b : Term Φ 1) :
    atIndex i (composeTerm a b) = .let₁ (atIndex i a) (atIndex 0 b) := by
  simp only [atIndex, composeTerm, continuation, Tm.rename, Tm.rename_comp]
  congr 1
  apply Tm.rename_congr
  intro i
  have hi := Fin.eq_zero i
  subst i
  rfl

/-- Singleton computations may ignore any number of unused older slots. -/
def atZeroDeriv {n : Nat} (Γ : QCtx τ n) {e : ε} {a : Term Φ 1} {A B : τ}
    (ha : HasType F (input A) e a B) :
    HasType F (Γ.zero.snoc A) e (atIndex 0 a) B := by
  have hw := (QCtx.discardable_iff_weakening_nil.mp (QCtx.zero_discardable Γ)).up A
  have h := ha.rename _ hw
  convert h using 1
  apply Tm.rename_congr
  intro i
  have hi := Fin.eq_zero i
  subst i
  rfl

def leftBody {n : Nat} (a : Term Φ 1) : Term Φ (n + 2) := .pair (.bv 1) (atIndex 0 a)

theorem atIndex_leftTerm {n : Nat} (i : Fin n) (a : Term Φ 1) :
    atIndex i (leftTerm a) = .let₂ (.bv i) (leftBody a) := by
  simp only [atIndex, leftTerm, Tm.rename, onRight, Tm.rename_comp, leftBody]
  congr 2
  apply Tm.rename_congr
  intro j
  have hj := Fin.eq_zero j
  subst j
  rfl

theorem leftBody_underTwoBinders {n : Nat} (a : Term Φ 1) :
    (leftBody (n := n) a).underTwoBinders = leftBody (n := n + 1) a := by
  unfold leftBody
  simp only [Tm.underTwoBinders, Tm.rename, rename_atIndex]
  rfl

def leftBodyDeriv {n : Nat} (Γ : QCtx τ n) (A : τ) {e : ε}
    {a : Term Φ 1} {B C : τ} (ha : HasType F (input B) e a C) :
    HasType F ((Γ.zero.snoc A).snoc B) e (leftBody a) (product A C) := by
  have hs : Γ.zero.Split Γ.zero Γ.zero := fun _ => ⟨rfl, rfl, .left .zero⟩
  apply HasType.pair ((hs.snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
  · apply singleVariable ((Γ.zero.snoc A).snoc B .zero) 1 e rfl
    intro j hj
    refine Fin.cases (fun _ => rfl) (fun k hk => ?_) j hj
    exact Fin.cases (fun h => False.elim (h rfl)) (fun _ _ => rfl) k hk
  · have ht := atZeroDeriv (Γ.snoc A) ha
    convert ht using 1
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem instantiate_leftBody {n : Nat} (a b : Term Φ n) (c : Term Φ 1) :
    Tm.instantiate (.let₁ b.lift (leftBody c)) a = .let₁ b (.pair a.lift (atIndex 0 c)) := by
  change Tm.let₁ (Tm.instantiate b.lift a)
    (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) (leftBody c)) = _
  rw [instantiate_lift]
  congr 1
  change Tm.pair (Tm.upSub (Fin.cases a Tm.bv) 1)
    (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) (atIndex 0 c)) = _
  congr 1
  simp only [atIndex, Tm.bsubst_rename]
  exact Tm.bsubst_bv_eq_rename (fun _ => 0) c

/-- Executing a tensor action after forming its input pair retains the pure
left value and sequences precisely the right computation. -/
theorem pair_then_left {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {c : Term Φ 1} {A B C : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl (⊥ : ε) a A) (hb : HasType F Γr (⊤ : ε) b B)
    (hc : HasType F (input B) (⊤ : ε) c C) (hq : quantity A ≤ Γl.linearity) :
    Equates (ε := ε) F R Γ
      (.let₁ (.pair a b) (atIndex 0 (leftTerm c)))
      (.pair a (.let₁ b (atIndex 0 c))) (product A C) := by
  have hp := HasType.pair s ha.top hb
  have hbody := leftBodyDeriv Γ A hc
  have hmid : WellTyped (ε := ε) F Γ (.let₂ (.pair a b) (leftBody c)) (product A C) :=
    ⟨.let₂ (QCtx.Split.zero_left Γ) hp hbody⟩
  have hinput : WellTyped (ε := ε) F Γ
      (.let₁ (.pair a b) (atIndex 0 (leftTerm c))) (product A C) :=
    ⟨.let₁ (QCtx.Split.zero_left Γ) hp (atZeroDeriv Γ (leftDeriv A hc))⟩
  have hbind := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBind (QCtx.Split.zero_left Γ) hp hbody) hmid
    (by simpa only [atIndex_leftTerm, leftBody_underTwoBinders] using hinput)
  have hbLift := hb.rename Fin.succ (.insertZero Γr A)
  rw [show Tm.rename Fin.succ b = b.lift from rfl] at hbLift
  have hseq := HasType.let₁ ((QCtx.Split.zero_left Γr).snoc (.left (.used ⊤)))
    hbLift (leftBodyDeriv Γr A hc)
  have hbeta := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBeta (QCtx.Split.zero_right Γ) s ha.top hb hbody)
    hmid (show WellTyped (ε := ε) F Γ _ _ from ⟨.let₁ s.symm ha.top hseq⟩)
  have hpost := pair_let_right (R := R) s (QCtx.Split.zero_left Γr) ha hb (atZeroDeriv Γr hc)
  have hsubst := pureBeta (R := R) s ha hseq hq
    (by simpa only [instantiate_leftBody] using hpost.1.wellTyped.2)
  have hbind' : Equates (ε := ε) F R Γ
      (.let₂ (.pair a b) (leftBody c))
      (.let₁ (.pair a b) (atIndex 0 (leftTerm c))) (product A C) := by
    simpa only [atIndex_leftTerm, leftBody_underTwoBinders] using hbind
  have hsubst' : Equates (ε := ε) F R Γ
      (.let₁ a (.let₁ b.lift (leftBody c)))
      (.let₁ b (.pair a.lift (atIndex 0 c))) (product A C) := by
    simpa only [instantiate_leftBody] using hsubst
  exact ((hbind'.symm.trans hbeta).trans hsubst').trans hpost.symm

theorem underBinder_atIndex_zero {n : Nat} (a : Term Φ 1) :
    (atIndex (0 : Fin (n + 1)) a).underBinder = atIndex 0 a := by
  unfold Tm.underBinder
  rw [rename_atIndex]
  rfl

def rightBody {n : Nat} (a : Term Φ 1) : Term Φ (n + 2) := .pair (atIndex 1 a) (.bv 0)

theorem atIndex_rightTerm {n : Nat} (i : Fin n) (a : Term Φ 1) :
    atIndex i (rightTerm a) = .let₂ (.bv i) (rightBody a) := by
  simp only [atIndex, rightTerm, Tm.rename, onLeft, Tm.rename_comp, rightBody]
  congr 2
  apply Tm.rename_congr
  intro j
  have hj := Fin.eq_zero j
  subst j
  rfl

theorem rightBody_underTwoBinders {n : Nat} (a : Term Φ 1) :
    (rightBody (n := n) a).underTwoBinders = rightBody (n := n + 1) a := by
  unfold rightBody
  simp only [Tm.underTwoBinders, Tm.rename, rename_atIndex]
  rfl

def rightBodyDeriv {n : Nat} (Γ : QCtx τ n) {e : ε}
    {a : Term Φ 1} {A B : τ} (ha : HasType F (input A) e a B) (C : τ) :
    HasType F ((Γ.zero.snoc A).snoc C) e (rightBody a) (product B C) := by
  have hs : Γ.zero.Split Γ.zero Γ.zero := fun _ => ⟨rfl, rfl, .left .zero⟩
  apply HasType.pair ((hs.snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
  · have ht := (atZeroDeriv Γ ha).rename Fin.succ (.insertZero (Γ.zero.snoc A) C)
    simpa only [rename_atIndex, show (Fin.succ 0 : Fin (n + 2)) = 1 from rfl] using ht
  · apply singleVariable ((Γ.zero.snoc A .zero).snoc C) 0 e rfl
    intro j hj
    refine Fin.cases (fun h => False.elim (h rfl)) (fun k _ => ?_) j hj
    exact Fin.cases rfl (fun _ => rfl) k

theorem instantiate_rightBody {n : Nat} (a : Term Φ (n + 1)) (b : Term Φ 1) :
    Tm.instantiate (rightBody (n := n) b) a = .pair (atIndex 0 b) a := by
  change Tm.pair (Tm.bsubst (Fin.cases a Tm.bv) (atIndex 1 b)) a = _
  congr 1
  simp only [atIndex, Tm.bsubst_rename]
  exact Tm.bsubst_bv_eq_rename (fun _ => 0) b

/-- Right tensor after a pair sequences its left computation and retains its
pure right component. -/
theorem pair_then_right {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {c : Term Φ 1} {A B C : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl (⊤ : ε) a A) (hb : HasType F Γr (⊥ : ε) b B)
    (hc : HasType F (input A) (⊤ : ε) c C) (hq : quantity B ≤ Γr.linearity) :
    Equates (ε := ε) F R Γ
      (.let₁ (.pair a b) (atIndex 0 (rightTerm c)))
      (.pair (.let₁ a (atIndex 0 c)) b) (product C B) := by
  have hp := HasType.pair s ha hb.top
  have hbody := rightBodyDeriv Γ hc B
  have hmid : WellTyped (ε := ε) F Γ (.let₂ (.pair a b) (rightBody c)) (product C B) :=
    ⟨.let₂ (QCtx.Split.zero_left Γ) hp hbody⟩
  have hinput : WellTyped (ε := ε) F Γ
      (.let₁ (.pair a b) (atIndex 0 (rightTerm c))) (product C B) :=
    ⟨.let₁ (QCtx.Split.zero_left Γ) hp (atZeroDeriv Γ (rightDeriv B hc))⟩
  have hbind := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBind (QCtx.Split.zero_left Γ) hp hbody) hmid
    (by simpa only [atIndex_rightTerm, rightBody_underTwoBinders] using hinput)
  have hbLift := hb.rename Fin.succ (.insertZero Γr A)
  rw [show Tm.rename Fin.succ b = b.lift from rfl] at hbLift
  have hs := (QCtx.Split.zero_left Γr).snoc (A := A) (QCtx.SlotSplit.left (.used ⊤))
  have hseq := HasType.let₁ hs hbLift.top (rightBodyDeriv Γr hc B)
  have hbeta := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBeta (QCtx.Split.zero_right Γ) s ha hb.top hbody)
    hmid (show WellTyped (ε := ε) F Γ _ _ from ⟨.let₁ s.symm ha hseq⟩)
  have hpost := pair_let_left (R := R) s (QCtx.Split.zero_left Γl) ha (atZeroDeriv Γl hc) hb
  have hq' : quantity B ≤ (Γr.snoc A .zero).linearity := by
    rw [QCtx.linearity_snoc]
    exact le_inf le_top hq
  have hsubst := pureBeta (R := R) hs.symm hbLift (rightBodyDeriv Γr hc B) hq'
    (by
      rw [instantiate_rightBody]
      exact ⟨.pair hs (atZeroDeriv Γr hc) hbLift.top⟩)
  have hbind' : Equates (ε := ε) F R Γ
      (.let₂ (.pair a b) (rightBody c))
      (.let₁ (.pair a b) (atIndex 0 (rightTerm c))) (product C B) := by
    simpa only [atIndex_rightTerm, rightBody_underTwoBinders] using hbind
  have hsubst' : Equates (ε := ε) F R (Γr.snoc A)
      (.let₁ b.lift (rightBody c)) (.pair (atIndex 0 c) b.lift) (product C B) := by
    simpa only [instantiate_rightBody] using hsubst
  have hcongr := Equates.let₁ s.symm (Equates.refl (R := R) ⟨ha⟩) hsubst'
  exact ((hbind'.symm.trans hbeta).trans hcongr).trans hpost.symm

end Silmaril.Isotope.Refinement.Models.Syntactic
