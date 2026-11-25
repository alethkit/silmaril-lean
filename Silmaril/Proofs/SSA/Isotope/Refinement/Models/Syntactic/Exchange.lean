module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Monoidal

/-! # Directed effect-sensitive tensor exchange

Pair sequencing keeps its evaluation order for arbitrary effects. Exchanging
independent computations uses the effect system's polarity-sensitive mover
relation; purity gives exchange equations in both directions.
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

/-- Pairing sequences its left component before its right component for any
effects. The final product constructor is pure and uses its parameter once. -/
theorem pair_left_bind_any {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {A B : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl (⊤ : ε) a A) (hb : HasType F Γr (⊤ : ε) b B) :
    Equates (ε := ε) F R Γ (.pair a b) (.let₁ a (.pair (.bv 0) b.lift)) (product A B) := by
  have hqA : Usage.effective (.used .linear) (quantity A) ≤
      Usage.effective (.used ⊤) (quantity A) := by
    change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
    exact inf_le_inf bot_le le_rfl
  have hqB : Usage.effective (.used .linear) (quantity B) ≤
      Usage.effective (.used ⊤) (quantity B) := by
    change Quantity.linear ⊓ quantity B ≤ ⊤ ⊓ quantity B
    exact inf_le_inf bot_le le_rfl
  have hp := zeroParameter (F := F) (Φ := Φ) Γr A (.used ⊤) (⊥ : ε) hqA
  have hbLift := hb.rename Fin.succ (.insertZero Γr A)
  rw [show Tm.rename Fin.succ b = b.lift from rfl] at hbLift
  have hsplit := ((QCtx.Split.zero_left Γr).snoc (A := A) (.left (.used ⊤))).symm
  have he : Tm.instantiate (Tm.pair (.bv 1) (.bv 0) : Term Φ (n + 2)) b.lift =
      .pair (.bv 0) b.lift := rfl
  have hvar : Tm.lift (.bv 0 : Term Φ (n + 1)) = .bv 1 := rfl
  have hβ := linearBeta (R := R) hsplit hbLift
    (pairRightBindDeriv hp B (.used .linear) le_rfl)
    (pairRightBindDeriv hp B (.used ⊤) hqB)
    (EffectSystem.pure_commutes (⊤ : ε)).symm
    (by rw [hvar, he]; exact ⟨pairLeftBindDeriv hb A (.used ⊤) hqA⟩)
  have hβ' : Equates (ε := ε) F R (Γr.snoc A)
      (.let₁ b.lift (.pair (.bv 1) (.bv 0))) (.pair (.bv 0) b.lift) (product A B) := by
    simpa only [hvar, he] using hβ
  exact (pair_sequence (R := R) s ha hb).trans
    (Equates.let₁ s.symm (Equates.refl ⟨ha⟩) hβ')

/-- Left tensor applied to a computed pair preserves the order of both input
computations. No effect commutation or type-linearity bound is required. -/
theorem pair_then_left_any {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {c : Term Φ 1} {A B C : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl (⊤ : ε) a A) (hb : HasType F Γr (⊤ : ε) b B)
    (hc : HasType F (input B) (⊤ : ε) c C) :
    Equates (ε := ε) F R Γ
      (.let₁ (.pair a b) (atIndex 0 (leftTerm c)))
      (.pair a (.let₁ b (atIndex 0 c))) (product A C) := by
  have hp := HasType.pair s ha hb
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
    (EquationAxiom.pairBeta (QCtx.Split.zero_right Γ) s ha hb hbody)
    hmid (show WellTyped (ε := ε) F Γ _ _ from ⟨.let₁ s.symm ha hseq⟩)
  have hg := HasType.let₁ (QCtx.Split.zero_left Γr) hb (atZeroDeriv Γr hc)
  have hnormal := pair_left_bind_any (R := R) s ha hg
  have hq : Usage.effective (.used .linear) (quantity A) ≤
      Usage.effective (.used ⊤) (quantity A) := by
    change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
    exact inf_le_inf bot_le le_rfl
  have hstep := pair_let_right (R := R)
    ((QCtx.Split.zero_left Γr).snoc (A := A) (.left (.used ⊤)))
    (QCtx.Split.zero_left (Γr.snoc A .zero))
    (zeroParameter Γr A (.used ⊤) (⊥ : ε) hq) hbLift
    (atZeroDeriv (Γr.snoc A .zero) hc)
  have he : (Tm.let₁ b (atIndex 0 c)).lift = .let₁ b.lift (atIndex 0 c) := by
    change Tm.let₁ b.lift (Tm.rename (Tm.up Fin.succ) (atIndex 0 c)) = _
    rw [rename_atIndex]
    rfl
  have hstep' : Equates (ε := ε) F R (Γr.snoc A)
      (.pair (.bv 0) (Tm.let₁ b (atIndex 0 c)).lift)
      (.let₁ b.lift (leftBody c)) (product A C) := by
    simpa only [he, leftBody, show Tm.lift (.bv 0 : Term Φ (n + 1)) = .bv 1 from rfl] using hstep
  have hcongr := Equates.let₁ s.symm (Equates.refl (R := R) ⟨ha⟩) hstep'
  have hbind' : Equates (ε := ε) F R Γ
      (.let₂ (.pair a b) (leftBody c))
      (.let₁ (.pair a b) (atIndex 0 (leftTerm c))) (product A C) := by
    simpa only [atIndex_leftTerm, leftBody_underTwoBinders] using hbind
  exact (hbind'.symm.trans hbeta).trans (hnormal.trans hcongr).symm

/-- Moving a let out of the left component preserves evaluation order even
when the retained right component is effectful. -/
theorem pair_let_left_any {n : Nat} {Γ Γab Γc Γa Γb : QCtx τ n}
    {a c : Term Φ n} {b : Term Φ (n + 1)} {A B C : τ}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γb Γa)
    (ha : HasType F Γa (⊤ : ε) a A) (hb : HasType F (Γb.snoc A) (⊤ : ε) b B)
    (hc : HasType F Γc (⊤ : ε) c C) :
    Equates (ε := ε) F R Γ (.pair (.let₁ a b) c)
      (.let₁ a (.pair b c.lift)) (product B C) := by
  have hlift : Tm.rename Fin.succ c = c.lift := rfl
  have hp : (Tm.pair (.bv 0) c.lift).underBinder = .pair (.bv 0) c.lift.lift := by
    change Tm.pair (.bv 0) (Tm.rename (Tm.up Fin.succ) c.lift) = _
    rw [Tm.rename_lift]
    rfl
  obtain ⟨Γcb, hs, ht⟩ := s.symm.assoc t
  have hinit := pair_left_bind_any (R := R) s (HasType.let₁ t ha hb) hc
  have hq : Usage.effective (.used .linear) (quantity B) ≤
      Usage.effective (.used ⊤) (quantity B) := by
    change Quantity.linear ⊓ quantity B ≤ ⊤ ⊓ quantity B
    exact inf_le_inf bot_le le_rfl
  have hend := pair_left_bind_any (R := R) (ht.symm.snoc (.left (.used ⊤))) hb
    (hc.rename Fin.succ (.insertZero Γc A))
  have hmid : WellTyped (ε := ε) F Γ
      (.let₁ a (.let₁ b (Tm.pair (.bv 0) c.lift).underBinder)) (product B C) := by
    have h := HasType.let₁ hs ha hend.1.wellTyped.2.some
    simpa only [hp, hlift] using (show WellTyped (ε := ε) _ _ _ _ from ⟨h⟩)
  have hassoc := Equates.ofAxiom (R := R)
    (EquationAxiom.letLet hs ht ha hb (pairLeftBindDeriv hc B (.used ⊤) hq))
    hinit.1.wellTyped.2 hmid
  have hcongr : Equates (ε := ε) F R Γ
      (.let₁ a (.pair b c.lift)) (.let₁ a (.let₁ b (Tm.pair (.bv 0) c.lift).underBinder))
      (product B C) := by
    simpa only [hp, hlift] using Equates.let₁ hs (Equates.refl (R := R) ⟨ha⟩) hend
  exact (hinit.trans hassoc).trans hcongr.symm

/-- The retained result of a right tensor action is used exactly once. -/
def rightBodyLinearDeriv {n : Nat} (Γ : QCtx τ n) {e : ε}
    {a : Term Φ 1} {A B : τ} (ha : HasType F (input A) e a B) (C : τ) :
    HasType F ((Γ.zero.snoc A).snoc C (.used .linear)) e (rightBody a) (product B C) := by
  have hs : Γ.zero.Split Γ.zero Γ.zero := fun _ => ⟨rfl, rfl, .left .zero⟩
  apply HasType.pair ((hs.snoc (.left (.used ⊤))).snoc (.right (.used .linear)))
  · have ht := (atZeroDeriv Γ ha).rename Fin.succ (.insertZero (Γ.zero.snoc A) C)
    simpa only [rename_atIndex, show (Fin.succ 0 : Fin (n + 2)) = 1 from rfl] using ht
  · have ht := zeroParameter (F := F) (Φ := Φ) (Γ.snoc A) C (.used .linear) e le_rfl
    convert ht using 1
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- The sole reordering step of tensor exchange, with precisely the written
polarity-sensitive mover premise and a linear use of the retained result. -/
theorem pair_then_right_moves {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {c : Term Φ 1} {A B C : τ} {e η : ε} (p : Polarity)
    (s : Γ.Split Γl Γr) (ha : HasType F Γl (⊤ : ε) a A)
    (hb : HasType F Γr e b B) (hc : HasType F (input A) η c C)
    (hm : EffectSystem.moves p e η) :
    p.orient (fun x y => Refines (ε := ε) F R Γ x y (product C B))
      (.let₁ (.pair a b) (atIndex 0 (rightTerm c)))
      (.pair (.let₁ a (atIndex 0 c)) b) := by
  have hp := HasType.pair s ha hb.top
  have hbody := rightBodyDeriv Γ hc.top B
  have hmid : WellTyped (ε := ε) F Γ (.let₂ (.pair a b) (rightBody c)) (product C B) :=
    ⟨.let₂ (QCtx.Split.zero_left Γ) hp hbody⟩
  have hinput : WellTyped (ε := ε) F Γ
      (.let₁ (.pair a b) (atIndex 0 (rightTerm c))) (product C B) :=
    ⟨.let₁ (QCtx.Split.zero_left Γ) hp (atZeroDeriv Γ (rightDeriv B hc.top))⟩
  have hbind := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBind (QCtx.Split.zero_left Γ) hp hbody) hmid
    (by simpa only [atIndex_rightTerm, rightBody_underTwoBinders] using hinput)
  have hbLift := hb.rename Fin.succ (.insertZero Γr A)
  rw [show Tm.rename Fin.succ b = b.lift from rfl] at hbLift
  have hs := (QCtx.Split.zero_left Γr).snoc (A := A) (QCtx.SlotSplit.left (.used ⊤))
  have hseq := HasType.let₁ hs hbLift.top (rightBodyDeriv Γr hc.top B)
  have hbeta := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBeta (QCtx.Split.zero_right Γ) s ha hb.top hbody)
    hmid (show WellTyped (ε := ε) F Γ _ _ from ⟨.let₁ s.symm ha hseq⟩)
  have hpost := pair_let_left_any (R := R) s (QCtx.Split.zero_left Γl) ha
    (atZeroDeriv Γl hc.top) hb.top
  have hβ : DirectionalAxiom (ε := ε) F p (Γr.snoc A)
      (.let₁ b.lift (rightBody c)) (.pair (atIndex 0 c) b.lift) (product C B) := by
    simpa only [instantiate_rightBody] using
      DirectionalAxiom.beta hs.symm hbLift (rightBodyLinearDeriv Γr hc B)
        (rightBodyDeriv Γr hc B) hm ((Usage.used_le_used _ _).2 bot_le)
  have hout : WellTyped (ε := ε) F (Γr.snoc A) (.pair (atIndex 0 c) b.lift) (product C B) :=
    ⟨.pair hs (atZeroDeriv Γr hc.top) hbLift.top⟩
  have hsubst := Refines.directional (R := R) p hβ ⟨hseq⟩ hout
  have hbind' : Equates (ε := ε) F R Γ
      (.let₂ (.pair a b) (rightBody c))
      (.let₁ (.pair a b) (atIndex 0 (rightTerm c))) (product C B) := by
    simpa only [atIndex_rightTerm, rightBody_underTwoBinders] using hbind
  have hleft := hbind'.symm.trans hbeta
  cases p with
  | positive => exact hleft.1.trans ((Refines.let₁ s.symm (.refl ⟨ha⟩) hsubst).trans hpost.2)
  | negative => exact hpost.1.trans ((Refines.let₁ s.symm (.refl ⟨ha⟩) hsubst).trans hleft.2)

/-- Composition after destructuring the input pair moves inside that binder. -/
theorem destruct_compose {A B C D : τ} {c : Term Φ 3} {d : Term Φ 1}
    (hc : HasType F (pairContext (product A B) A B) (⊤ : ε) c C)
    (hd : HasType F (input C) (⊤ : ε) d D) :
    Equates (ε := ε) F R (input (product A B))
      (composeTerm (.let₂ (.bv 0) c) d) (.let₂ (.bv 0) (.let₁ c (atIndex 0 d))) D := by
  let P := product A B
  have hinput := composeDeriv (HasType.let₂ (inputSplit P) (identityDeriv P (⊤ : ε)) hc) hd
  have hmid : WellTyped (ε := ε) F (input P) (.let₂ (.bv 0) (.let₁ c (atIndex 0 d))) D :=
    ⟨.let₂ (inputSplit P) (identityDeriv P ⊤)
      (.let₁ (QCtx.Split.zero_left (pairContext P A B)) hc (atZeroDeriv (pairContext P A B) hd))⟩
  have hdc := hd.rename _ ((QCtx.Weakening.insertZero QCtx.nil P).up C)
  have h := Equates.ofAxiom (R := R)
    (EquationAxiom.letLetPair (inputSplit P) (QCtx.Split.nil.snoc (.left .zero))
      (identityDeriv P (⊤ : ε)) hc hdc) ⟨hinput⟩
    (by
      change WellTyped (ε := ε) F (input P)
        (.let₂ (.bv 0) (.let₁ c (continuation d).underBinder.underBinder)) D
      simpa only [continuation_atIndex, underBinder_atIndex_zero] using hmid)
  change Equates (ε := ε) F R (input P) (composeTerm (.let₂ (.bv 0) c) d)
    (.let₂ (.bv 0) (.let₁ c (continuation d).underBinder.underBinder)) D at h
  simpa only [continuation_atIndex, underBinder_atIndex_zero] using h

/-- The singleton identity equation transported to any quantitative context. -/
theorem singleton_identity (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n}
    {A B : τ} (a : Arrow (Φ := Φ) (ε := ε) F A B) (ρ : Fin 1 → Fin n)
    (hw : QCtx.Weakening Γ (input A) ρ) :
    Equates (ε := ε) F R Γ (.let₁ (.bv (ρ 0)) (atIndex 0 a.val)) (Tm.rename ρ a.val) B := by
  have h := (identity_compose_equates R a).rename ρ hw hR
  change Equates (ε := ε) F R Γ
    (Tm.rename ρ (composeTerm (.bv 0) a.val)) (Tm.rename ρ a.val) B at h
  simpa only [composeTerm, Tm.rename, continuation_atIndex, rename_atIndex,
    show Tm.up ρ 0 = 0 from rfl] using h

/-- Left sequential tensor evaluates the left computation and then the right
computation, represented by the ordinary ordered pair. -/
theorem tensor_left_normal (hR : R.RenamingClosed) {A B C D : τ}
    (a : Arrow (Φ := Φ) (ε := ε) F A B) (b : Arrow (Φ := Φ) (ε := ε) F C D) :
    Equates (ε := ε) F R (input (product A C))
      (composeArrow (rightArrow a C) (leftArrow B b)).val
      (.let₂ (.bv 0) (.pair (onLeft a.val) (onRight b.val))) (product B D) := by
  obtain ⟨da⟩ := a.property
  obtain ⟨db⟩ := b.property
  let P := product A C
  have dal : HasType F (pairLeftContext P A C) (⊤ : ε) (onLeft a.val) B :=
    da.rename _ (.skip (.cons (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl)
  have hl := pair_then_left_any (R := R) (pairSplit P A C) dal (rightParameter P A C ⊤) db
  have hid := singleton_identity (R := R) hR b _
    (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl :
      QCtx.Weakening (pairRightContext P A C) (input C)
        (Tm.up (fun i : Fin 0 => i.succ.succ)))
  have hp := Equates.pair (pairSplit P A C) (Equates.refl (R := R) ⟨dal⟩) hid
  have hbody := hl.trans hp
  have houter := Equates.let₂ (inputSplit P) (Equates.refl (R := R) ⟨identityDeriv P (⊤ : ε)⟩) hbody
  have hdestruct := destruct_compose (R := R)
    (HasType.pair (pairSplit P A C) dal (rightParameter P A C ⊤)) (leftDeriv B db)
  exact hdestruct.trans houter

/-- Native right-mover exchange between the two sequential tensor orders. -/
theorem tensor_exchange_refines (hR : R.RenamingClosed) (p : Polarity)
    {A B C D : τ} {e η : ε}
    (a : Arrow (Φ := Φ) (ε := ε) F A B) (b : Arrow (Φ := Φ) (ε := ε) F C D)
    (da : HasType F (input A) e a.val B) (db : HasType F (input C) η b.val D)
    (hm : EffectSystem.moves p e η) :
    p.orient (fun x y => Refines (ε := ε) F R (input (product A C)) x y (product B D))
      (composeArrow (rightArrow a C) (leftArrow B b)).val
      (composeArrow (leftArrow A b) (rightArrow a D)).val := by
  let P := product A C
  have dbr : HasType F (pairRightContext P A C) η (onRight b.val) D :=
    db.rename _ (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl)
  have hm' : EffectSystem.moves p.reverse η e := (EffectSystem.moves_reverse p η e).2 hm
  have hmove := pair_then_right_moves (R := R) p.reverse (pairSplit P A C)
    (leftParameter P A C (⊤ : ε)) dbr da hm'
  have hid := singleton_identity (R := R) hR a _
    (.skip (.cons (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl :
      QCtx.Weakening (pairLeftContext P A C) (input A)
        (fun i => (Tm.up (Fin.succ : Fin 0 → Fin 1) i).succ))
  change Equates (ε := ε) F R (pairLeftContext P A C)
    (.let₁ (.bv 1) (atIndex 0 a.val)) (onLeft a.val) B at hid
  have hpair := Equates.pair (pairSplit P A C) hid (Equates.refl (R := R) ⟨dbr.top⟩)
  have hleft := tensor_left_normal (R := R) hR a b
  have hright := destruct_compose (R := R)
    (HasType.pair (pairSplit P A C) (leftParameter P A C (⊤ : ε)) dbr.top)
    (rightDeriv D da.top)
  cases p with
  | positive =>
    exact hleft.1.trans ((Refines.let₂ (inputSplit P) (.refl ⟨identityDeriv P (⊤ : ε)⟩)
      (hpair.2.trans hmove)).trans hright.2)
  | negative =>
    exact hright.1.trans ((Refines.let₂ (inputSplit P) (.refl ⟨identityDeriv P (⊤ : ε)⟩)
      (hmove.trans hpair.1)).trans hleft.2)

/-- The quotient inherits exactly the effect system's directed exchange law. -/
theorem tensor_exchange (hR : R.RenamingClosed) (p : Polarity)
    {A B C D : τ} {e η : ε}
    {a : Hom (ε := ε) F R A B} {b : Hom (ε := ε) F R C D}
    (hm : EffectSystem.moves p e η) (ha : hasEffect e a) (hb : hasEffect η b) :
    p.orient (· ≤ ·)
      (compose hR (right hR a C) (left hR B b))
      (compose hR (left hR A b) (right hR a D)) := by
  obtain ⟨a, rfl, ⟨da⟩⟩ := ha
  obtain ⟨b, rfl, ⟨db⟩⟩ := hb
  exact tensor_exchange_refines hR p a b da db hm

/-- A pure left computation exchanges with every right computation. -/
theorem pure_exchange_left (hR : R.RenamingClosed) {A B C D : τ}
    {a : Hom (ε := ε) F R A B} (ha : hasEffect (⊥ : ε) a)
    (b : Hom (ε := ε) F R C D) :
    compose hR (right hR a C) (left hR B b) =
      compose hR (left hR A b) (right hR a D) :=
  le_antisymm
    (tensor_exchange hR .positive (EffectSystem.pure_moves .positive ⊤) ha (hasEffect_top b))
    (tensor_exchange hR .negative (EffectSystem.pure_moves .negative ⊤) ha (hasEffect_top b))

/-- A pure right computation exchanges with every left computation. -/
theorem pure_exchange_right (hR : R.RenamingClosed) {A B C D : τ}
    (a : Hom (ε := ε) F R A B) {b : Hom (ε := ε) F R C D} (hb : hasEffect (⊥ : ε) b) :
    compose hR (right hR a C) (left hR B b) =
      compose hR (left hR A b) (right hR a D) :=
  le_antisymm
    (tensor_exchange hR .positive (EffectSystem.moves_pure .positive ⊤) (hasEffect_top a) hb)
    (tensor_exchange hR .negative (EffectSystem.moves_pure .negative ⊤) (hasEffect_top a) hb)

end Silmaril.Isotope.Refinement.Models.Syntactic
