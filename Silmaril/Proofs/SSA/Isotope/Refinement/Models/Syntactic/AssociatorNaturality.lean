module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Naturality
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.AssociatorReduction
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.MixedBeta

/-! # Separate naturality of the syntactic associator -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

def assocBody {n : Nat} : Term Φ (n + 2) :=
  .let₂ (.bv 1) (.pair (.bv 1) (.pair (.bv 0) (.bv 2)))

theorem atIndex_assocTerm {n : Nat} (i : Fin n) :
    atIndex i (assocTerm (Φ := Φ)) = .let₂ (.bv i) assocBody := rfl

/-- Reassociation consumes its rightmost parameter linearly, even when the
ambient type supports copying or discarding. -/
def assocBodyUsageDeriv {n : Nat} (Γ : QCtx τ n) (A B C : τ) (q : Usage) (e : ε)
    (hq : Usage.effective (.used .linear) (quantity C) ≤ Usage.effective q (quantity C)) :
    HasType F ((Γ.zero.snoc (product A B)).snoc C q) e
      (assocBody (Φ := Φ)) (product A (product B C)) := by
  have hz : Γ.zero.Split Γ.zero Γ.zero := fun _ => ⟨rfl, rfl, .left .zero⟩
  apply HasType.let₂ ((hz.snoc (.right (.used ⊤))).snoc (.left q))
  · exact (atZeroDeriv Γ (identityDeriv (F := F) (Φ := Φ) (product A B) e)).rename Fin.succ
      (.insertZero _ C)
  · apply HasType.pair
      ((((hz.snoc (.left .zero)).snoc (.right q)).snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
    · apply singleVariable _ 1 e rfl
      intro j hj
      refine Fin.cases (fun _ => rfl) (fun k hk => ?_) j hj
      refine Fin.cases (fun h => False.elim (h rfl)) (fun l _ => ?_) k hk
      exact Fin.cases rfl (fun l => Fin.cases rfl (fun _ => rfl) l) l
    · apply HasType.pair
        ((((hz.snoc (.left .zero)).snoc (.right q)).snoc (.left .zero)).snoc (.left (.used ⊤)))
      · apply singleVariable _ 0 e rfl
        intro j hj
        refine Fin.cases (fun h => False.elim (h rfl)) (fun k _ => ?_) j hj
        exact Fin.cases rfl (fun l => Fin.cases rfl (fun l => Fin.cases rfl (fun _ => rfl) l) l) k
      · have dc : HasType F ((Γ.zero.snoc (product A B) .zero).snoc C q) e
            (.bv 0 : Term Φ (n + 2)) C := by
          convert zeroParameter (F := F) (Φ := Φ) (Γ.snoc (product A B)) C q e hq using 1
          congr 1
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        exact (dc.rename Fin.succ (.insertZero _ A)).rename Fin.succ (.insertZero _ B)

/-- Applying reassociation after a pure left product and arbitrary right
computation expands the left product without changing the computation order. -/
theorem pair_then_assoc {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {A B C : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl (⊥ : ε) a (product A B)) (hb : HasType F Γr (⊤ : ε) b C)
    (hq : quantity (product A B) ≤ Γl.linearity) :
    Equates (ε := ε) F R Γ
      (.let₁ (.pair a b) (atIndex 0 (assocTerm (Φ := Φ))))
      (.let₂ a (.pair (.bv 1) (.pair (.bv 0) b.lift.lift))) (product A (product B C)) := by
  have hc := assocBodyUsageDeriv (F := F) (Φ := Φ) Γ A B C (.used .linear) (⊥ : ε) le_rfl
  have hqd : Usage.effective (.used .linear) (quantity C) ≤
      Usage.effective (.used ⊤) (quantity C) := by
    change Quantity.linear ⊓ quantity C ≤ ⊤ ⊓ quantity C
    exact inf_le_inf bot_le le_rfl
  have hd := assocBodyUsageDeriv (F := F) (Φ := Φ) Γ A B C (.used ⊤) (⊥ : ε) hqd
  have hp := HasType.pair s ha.top hb
  have hbind := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBind (QCtx.Split.zero_left Γ) hp hd.top)
    ⟨.let₂ (QCtx.Split.zero_left Γ) hp hd.top⟩
    (show WellTyped (ε := ε) F Γ
      (.let₁ (.pair a b) (atIndex 0 (assocTerm (Φ := Φ)))) (product A (product B C)) from
      ⟨.let₁ (QCtx.Split.zero_left Γ) hp (atZeroDeriv Γ (assocDeriv A B C (⊤ : ε)))⟩)
  have hβ := mixedPairBeta (R := R) (QCtx.Split.zero_right Γ) s ha hb hc hd hq
    (EffectSystem.pure_commutes (⊤ : ε)).symm
  have he : Tm.instantiate (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv))
      (assocBody (n := n) (Φ := Φ))) b =
      .let₂ a (.pair (.bv 1) (.pair (.bv 0) b.lift.lift)) := by
    change Tm.let₂ (Tm.instantiate a.lift b) (.pair (.bv 1) (.pair (.bv 0) b.lift.lift)) = _
    rw [instantiate_lift]
  have hbind' : Equates (ε := ε) F R Γ (.let₂ (.pair a b) assocBody)
      (.let₁ (.pair a b) (atIndex 0 (assocTerm (Φ := Φ)))) (product A (product B C)) := hbind
  exact hbind'.symm.trans (by simpa only [he] using hβ)

/-- A one-input continuation commutes under product elimination with the
resource split inherited from that elimination. -/
theorem pair_elim_then {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {b : Term Φ (n + 2)} {c : Term Φ 1} {A B C D : τ}
    (s : Γ.Split Γl Γr) (ha : HasType F Γr (⊤ : ε) a (product A B))
    (hb : HasType F ((Γl.snoc A).snoc B) (⊤ : ε) b C)
    (hc : HasType F (input C) (⊤ : ε) c D) :
    Equates (ε := ε) F R Γ (.let₁ (.let₂ a b) (atIndex 0 c))
      (.let₂ a (.let₁ b (atIndex 0 c))) D := by
  have h := let_pair (R := R) s (QCtx.Split.zero_left Γl) ha hb (atZeroDeriv Γl hc)
  simpa only [underBinder_atIndex_zero] using h

/-- Reassociation is natural in the rightmost, possibly effectful, component. -/
theorem assoc_natural_right_equates (hR : R.RenamingClosed) (A B : τ) {C D : τ}
    (f : Arrow (Φ := Φ) (ε := ε) F C D) :
    Equates (ε := ε) F R (input (product (product A B) C))
      (composeArrow (leftArrow (product A B) f) (assocArrow A B D)).val
      (composeArrow (assocArrow A B C) (leftArrow A (leftArrow B f))).val
      (product A (product B D)) := by
  obtain ⟨df⟩ := f.property
  let P := product (product A B) C
  have dfr : HasType F (pairRightContext P (product A B) C) (⊤ : ε) (onRight f.val) D :=
    df.rename _ (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl)
  have hq : quantity (product A B) ≤ (pairLeftContext P (product A B) C).linearity := by
    simp only [pairLeftContext, QCtx.linearity_snoc, Usage.linearity_zero,
      Usage.linearity_used, QCtx.linearity_nil, inf_top_eq]
    exact le_inf le_top (le_inf le_rfl le_top)
  have hl := pair_then_assoc (R := R) (pairSplit P (product A B) C)
    (leftParameter P (product A B) C (⊥ : ε)) dfr hq
  let Γa : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C .zero).snoc A).snoc B .zero
  let Γb : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C .zero).snoc A .zero).snoc B
  let Γc : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C).snoc A .zero).snoc B .zero
  have da : HasType F Γa (⊤ : ε) (.bv 1 : Term Φ 5) A :=
    singleVariable Γa 1 ⊤ rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have db : HasType F Γb (⊤ : ε) (.bv 0 : Term Φ 5) B :=
    singleVariable Γb 0 ⊤ rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dc : HasType F Γc (⊤ : ε) (.bv 2 : Term Φ 5) C :=
    singleVariable Γc 2 ⊤ rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have sbc := (((((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := product A B) (.left .zero)).snoc
    (A := C) (.right (.used ⊤))).snoc (A := A) (.left .zero)).snoc (A := B) (.left (.used ⊤)))
  have sabc := (((((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := product A B) (.left .zero)).snoc
    (A := C) (.right (.used ⊤))).snoc (A := A) (.left (.used ⊤))).snoc (A := B) (.right (.used ⊤)))
  have hw : QCtx.Weakening Γc (input C) (fun i =>
      (Tm.up (fun j : Fin 0 => j.succ.succ) i).succ.succ) :=
    .skip (.skip (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl
  have hw' : QCtx.Weakening Γc (input C) (fun _ => (2 : Fin 5)) := by
    convert hw using 1
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  have hi := singleton_identity (R := R) hR f _ hw'
  have hbc := (pair_then_left_any (R := R) sbc db dc df).trans
    (Equates.pair sbc (Equates.refl (R := R) ⟨db⟩) hi)
  have habc := (pair_then_left_any (R := R) sabc da (HasType.pair sbc db dc)
    (leftDeriv B df)).trans (Equates.pair sabc (Equates.refl (R := R) ⟨da⟩) hbc)
  have hunder := Equates.let₂ (pairSplit P (product A B) C).symm
    (Equates.refl (R := R) ⟨leftParameter P (product A B) C (⊤ : ε)⟩) habc
  have hr := (pair_elim_then (R := R) (pairSplit P (product A B) C).symm
    (leftParameter P (product A B) C (⊤ : ε)) (HasType.pair sabc da (HasType.pair sbc db dc))
    (leftDeriv A (leftDeriv B df))).trans hunder
  have he : (onRight f.val).lift.lift = atIndex (2 : Fin 5) f.val := by
    rw [onRight_atIndex]
    simp only [Tm.lift, rename_atIndex]
    rfl
  rw [he] at hl
  have hbody := hl.trans hr.symm
  have houter := Equates.let₂ (inputSplit P)
    (Equates.refl (R := R) ⟨identityDeriv P (⊤ : ε)⟩) hbody
  have hfirst := destruct_compose (R := R)
    (HasType.pair (pairSplit P (product A B) C) (leftParameter P (product A B) C (⊤ : ε)) dfr)
    (assocDeriv A B D (⊤ : ε))
  have hlast := destruct_compose (R := R) (assocBodyDeriv A B C (⊤ : ε))
    (leftDeriv A (leftDeriv B df))
  exact (hfirst.trans houter).trans hlast.symm

theorem assoc_natural_right (hR : R.RenamingClosed) (A B : τ) {C D : τ}
    (f : Hom (ε := ε) F R C D) :
    compose hR (left hR (product A B) f) (assoc A B D) =
      compose hR (assoc A B C) (left hR A (left hR B f)) := by
  induction f using Quotient.inductionOn with
  | _ f => exact Quotient.sound (assoc_natural_right_equates hR A B f)

end Silmaril.Isotope.Refinement.Models.Syntactic
