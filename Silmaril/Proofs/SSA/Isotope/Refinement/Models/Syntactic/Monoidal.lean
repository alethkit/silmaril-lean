module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.TensorSyntax

/-! # Functoriality of the native syntactic tensor actions

Both actions preserve composition by the written term equations, without an
interchange assumption for effectful computations.
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

/-- Left tensor preserves sequential composition already on typed representatives. -/
theorem left_compose_equates {A B C D : τ}
    (a : Arrow (Φ := Φ) (ε := ε) F B C) (b : Arrow (Φ := Φ) (ε := ε) F C D) :
    Equates (ε := ε) F R (input (product A B))
      (composeArrow (leftArrow A a) (leftArrow A b)).val
      (leftArrow A (composeArrow a b)).val (product A D) := by
  obtain ⟨da⟩ := a.property
  obtain ⟨db⟩ := b.property
  let P := product A B
  have dar : HasType F (pairRightContext P A B) (⊤ : ε) (onRight a.val) C :=
    da.rename _ (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl)
  have hq : quantity A ≤ (pairLeftContext P A B).linearity := by
    apply QCtx.le_linearity_iff.mpr
    intro i
    fin_cases i
    · exact le_top
    · exact le_inf le_rfl le_top
    · exact le_top
  have hl := pair_then_left (R := R) (pairSplit P A B)
    (leftParameter P A B (⊥ : ε)) dar db hq
  have hc : HasType F (pairContext P A B) (⊤ : ε)
      (.pair (.bv 1) (onRight a.val)) (product A C) :=
    .pair (pairSplit P A B) (leftParameter P A B ⊤) dar
  have hd := (leftDeriv A db).rename _ ((QCtx.Weakening.insertZero QCtx.nil P).up (product A C))
  have hmid : WellTyped (ε := ε) F (input P)
      (.let₂ (.bv 0) (.let₁ (.pair (.bv 1) (onRight a.val)) (atIndex 0 (leftTerm b.val))))
      (product A D) := ⟨.let₂ (inputSplit P) (identityDeriv P ⊤) hl.1.wellTyped.1.some⟩
  have he := Equates.ofAxiom (R := R)
    (EquationAxiom.letLetPair (inputSplit P) (QCtx.Split.nil.snoc (.left .zero))
      (identityDeriv P (⊤ : ε)) hc hd)
    (composeArrow (leftArrow A a) (leftArrow A b)).property
    (by
      change WellTyped (ε := ε) F (input P)
        (.let₂ (.bv 0) (.let₁ (.pair (.bv 1) (onRight a.val))
          (continuation (leftTerm b.val)).underBinder.underBinder)) (product A D)
      simpa only [continuation_atIndex, underBinder_atIndex_zero] using hmid)
  have he' : Equates (ε := ε) F R (input P)
      (composeArrow (leftArrow A a) (leftArrow A b)).val
      (.let₂ (.bv 0) (.let₁ (.pair (.bv 1) (onRight a.val)) (atIndex 0 (leftTerm b.val))))
      (product A D) := by
    change Equates (ε := ε) F R (input P)
      (composeArrow (leftArrow A a) (leftArrow A b)).val
      (.let₂ (.bv 0) (.let₁ (.pair (.bv 1) (onRight a.val))
        (continuation (leftTerm b.val)).underBinder.underBinder)) (product A D) at he
    simpa only [continuation_atIndex, underBinder_atIndex_zero] using he
  have hf := Equates.let₂ (inputSplit P) (Equates.refl (R := R) ⟨identityDeriv P (⊤ : ε)⟩) hl
  apply he'.trans
  simpa only [leftArrow, leftTerm, composeArrow, onRight_atIndex, atIndex_compose] using hf

/-- The quotient's left tensor action is a genuine functor on arrows. -/
theorem left_compose (hR : R.RenamingClosed) (A : τ) {B C D : τ}
    (a : Hom (ε := ε) F R B C) (b : Hom (ε := ε) F R C D) :
    left hR A (compose hR a b) = compose hR (left hR A a) (left hR A b) := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b => exact Quotient.sound (left_compose_equates (R := R) a b).symm

/-- Right tensor preserves composition on native typed representatives. -/
theorem compose_right_equates {A B C D : τ}
    (a : Arrow (Φ := Φ) (ε := ε) F A B) (b : Arrow (Φ := Φ) (ε := ε) F B C) :
    Equates (ε := ε) F R (input (product A D))
      (composeArrow (rightArrow a D) (rightArrow b D)).val
      (rightArrow (composeArrow a b) D).val (product C D) := by
  obtain ⟨da⟩ := a.property
  obtain ⟨db⟩ := b.property
  let P := product A D
  have dal : HasType F (pairLeftContext P A D) (⊤ : ε) (onLeft a.val) B :=
    da.rename _ (.skip (.cons (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl)
  have hq : quantity D ≤ (pairRightContext P A D).linearity := by
    apply QCtx.le_linearity_iff.mpr
    intro i
    fin_cases i
    · exact le_inf le_rfl le_top
    · exact le_top
    · exact le_top
  have hl := pair_then_right (R := R) (pairSplit P A D)
    dal (rightParameter P A D (⊥ : ε)) db hq
  have hc : HasType F (pairContext P A D) (⊤ : ε)
      (.pair (onLeft a.val) (.bv 0)) (product B D) :=
    .pair (pairSplit P A D) dal (rightParameter P A D ⊤)
  have hd := (rightDeriv D db).rename _ ((QCtx.Weakening.insertZero QCtx.nil P).up (product B D))
  have hmid : WellTyped (ε := ε) F (input P)
      (.let₂ (.bv 0) (.let₁ (.pair (onLeft a.val) (.bv 0)) (atIndex 0 (rightTerm b.val))))
      (product C D) := ⟨.let₂ (inputSplit P) (identityDeriv P ⊤) hl.1.wellTyped.1.some⟩
  have he := Equates.ofAxiom (R := R)
    (EquationAxiom.letLetPair (inputSplit P) (QCtx.Split.nil.snoc (.left .zero))
      (identityDeriv P (⊤ : ε)) hc hd)
    (composeArrow (rightArrow a D) (rightArrow b D)).property
    (by
      change WellTyped (ε := ε) F (input P)
        (.let₂ (.bv 0) (.let₁ (.pair (onLeft a.val) (.bv 0))
          (continuation (rightTerm b.val)).underBinder.underBinder)) (product C D)
      simpa only [continuation_atIndex, underBinder_atIndex_zero] using hmid)
  have he' : Equates (ε := ε) F R (input P)
      (composeArrow (rightArrow a D) (rightArrow b D)).val
      (.let₂ (.bv 0) (.let₁ (.pair (onLeft a.val) (.bv 0)) (atIndex 0 (rightTerm b.val))))
      (product C D) := by
    change Equates (ε := ε) F R (input P)
      (composeArrow (rightArrow a D) (rightArrow b D)).val
      (.let₂ (.bv 0) (.let₁ (.pair (onLeft a.val) (.bv 0))
        (continuation (rightTerm b.val)).underBinder.underBinder)) (product C D) at he
    simpa only [continuation_atIndex, underBinder_atIndex_zero] using he
  have hf := Equates.let₂ (inputSplit P) (Equates.refl (R := R) ⟨identityDeriv P (⊤ : ε)⟩) hl
  apply he'.trans
  simpa only [rightArrow, rightTerm, composeArrow, onLeft_atIndex, atIndex_compose] using hf

/-- The quotient's right tensor action preserves sequential composition. -/
theorem compose_right (hR : R.RenamingClosed) {A B C : τ}
    (a : Hom (ε := ε) F R A B) (b : Hom (ε := ε) F R B C) (D : τ) :
    right hR (compose hR a b) D = compose hR (right hR a D) (right hR b D) := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b => exact Quotient.sound (compose_right_equates (R := R) a b).symm

/-- Tensoring on the left is an actual functor on the native syntactic category. -/
def tensorLeftFunctor (hR : R.RenamingClosed) (A : τ) :
    Object ε F R hR ⥤ Object ε F R hR where
  obj X := ⟨product A X.type⟩
  map := left hR A
  map_id X := left_identity hR A X.type
  map_comp a b := left_compose hR A a b

/-- Tensoring on the right is an actual functor on the native syntactic category. -/
def tensorRightFunctor (hR : R.RenamingClosed) (A : τ) :
    Object ε F R hR ⥤ Object ε F R hR where
  obj X := ⟨product X.type A⟩
  map a := right hR a A
  map_id X := identity_right hR X.type A
  map_comp a b := compose_right hR a b A

end Silmaril.Isotope.Refinement.Models.Syntactic
