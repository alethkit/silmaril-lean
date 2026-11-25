module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterationDirectedEnvironment
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterationUniformity
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationCoaction
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionProjection

/-! # Left coactions for the written uniformity square -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Isotope.Refinement.Models
open CategoryTheory Denotation
open scoped MonoidalCategory PremonoidalCategory
universe u v w r

namespace Structural
open MonoidalCategory
variable {K : Type u} [Category.{v} K] [MonoidalCategory K]

/-- Left coassociativity with an additional state wire. -/
theorem left_coaction_duplicate {C D : K} (i : C ⟶ D ⊗ C) (c : D ⟶ D ⊗ D)
    (hi : i ≫ c ▷ C ≫ (α_ D D C).hom = i ≫ D ◁ i) (A : K) :
    i ▷ A ≫ (α_ D C A).hom ≫ D ◁ (i ▷ A ≫ (α_ D C A).hom) =
      i ▷ A ≫ (α_ D C A).hom ≫ c ▷ (C ⊗ A) ≫ (α_ D D (C ⊗ A)).hom := by
  simp only [whiskerLeft_comp]
  rw [← associator_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc, ← hi]
  simp only [comp_whiskerRight, Category.assoc]
  rw [pentagon]
  rw [← associator_naturality_left_assoc]

/-- Opposite coactions commute while retaining the state wire. -/
theorem mixed_coaction {C D : K} (i : C ⟶ D ⊗ C) (j : C ⟶ C ⊗ D)
    (hij : j ≫ i ▷ D ≫ (α_ D C D).hom = i ≫ D ◁ j) (A : K) :
    i ▷ A ≫ (α_ D C A).hom ≫ D ◁ (j ▷ A ≫ (α_ C D A).hom) =
      j ▷ A ≫ (α_ C D A).hom ≫ i ▷ (D ⊗ A) ≫ (α_ D C (D ⊗ A)).hom := by
  simp only [whiskerLeft_comp]
  rw [← associator_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc, ← hij]
  simp only [comp_whiskerRight, Category.assoc]
  rw [pentagon]
  rw [← associator_naturality_left_assoc]

/-- The left counit remains a counit after adjoining a state. -/
theorem left_coaction_counit {C D : K} (i : C ⟶ D ⊗ C) (d : D ⟶ 𝟙_ K)
    (hi : i ≫ d ▷ C ≫ (λ_ C).hom = 𝟙 C) (A : K) :
    i ▷ A ≫ (α_ D C A).hom ≫ d ▷ (C ⊗ A) ≫ (λ_ (C ⊗ A)).hom = 𝟙 (C ⊗ A) := by
  rw [← associator_naturality_left_assoc]
  have ht : (α_ (𝟙_ K) C A).hom ≫ (λ_ (C ⊗ A)).hom = (λ_ C).hom ▷ A := by monoidal
  rw [ht, ← comp_whiskerRight_assoc, ← comp_whiskerRight, Category.assoc, hi, id_whiskerRight]

end Structural

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- A pure context split with a state wire adjoined. -/
def contextAction {C D E : τ} (f : M.Hom C (product D E)) (A : τ) :
    M.Hom (product C A) (product D (product E A)) :=
  M.compose (M.right f A) (M.associator D E A)

theorem contextAction_pure {C D E : τ} (f : M.Hom C (product D E))
    (hf : M.hasEffect ⊥ f) (A : τ) : M.hasEffect ⊥ (M.contextAction f A) :=
  M.compose_effect (M.right_effect A hf) (M.associator_pure D E A)

theorem contextAction_natural {C D E A B : τ} (f : M.Hom C (product D E))
    (hf : M.hasEffect ⊥ f) (a : M.Hom A B) :
    M.compose (M.contextAction f A) (M.left D (M.left E a)) =
      M.compose (M.left C a) (M.contextAction f B) := by
  dsimp [contextAction]
  rw [M.compose_assoc, M.associator_natural_right, ← M.compose_assoc,
    M.exchange_left_pure f a hf, M.compose_assoc]

theorem contextAction_duplicate {C D : τ} (i : M.Hom C (product D C))
    (hi : M.hasEffect ⊥ i) (cD : Quantity.relevant ≤ quantity D)
    (hco : M.compose i (M.compose (M.right (M.copy D cD) C) (M.associator D D C)) =
      M.compose i (M.left D i)) (A : τ) :
    M.compose (M.contextAction i A) (M.left D (M.contextAction i A)) =
      M.compose (M.contextAction i A)
        (M.compose (M.right (M.copy D cD) (product C A)) (M.associator D D (product C A))) := by
  let C' : M.PureObject := ⟨C⟩
  let D' : M.PureObject := ⟨D⟩
  let A' : M.PureObject := ⟨A⟩
  let ii : C' ⟶ D' ⊗ C' := ⟨i, hi⟩
  let cc : D' ⟶ D' ⊗ D' := ⟨M.copy D cD, M.copy_pure D cD⟩
  have hco' : ii ≫ cc ▷ C' ≫ (α_ D' D' C').hom = ii ≫ D' ◁ ii := Subtype.ext hco
  have h := congrArg Subtype.val (Structural.left_coaction_duplicate ii cc hco' A')
  change M.compose (M.right i A)
    (M.compose (M.associator D C A) (M.left D (M.compose (M.right i A) (M.associator D C A)))) =
    M.compose (M.right i A) (M.compose (M.associator D C A)
      (M.compose (M.right (M.copy D cD) (product C A)) (M.associator D D (product C A)))) at h
  simpa only [contextAction, M.compose_assoc] using h

theorem contextAction_mixed {C D : τ} (i : M.Hom C (product D C)) (j : M.Hom C (product C D))
    (hi : M.hasEffect ⊥ i) (hj : M.hasEffect ⊥ j)
    (hco : M.compose j (M.compose (M.right i D) (M.associator D C D)) = M.compose i (M.left D j))
    (A : τ) :
    M.compose (M.contextAction i A) (M.left D (M.contextAction j A)) =
      M.compose (M.contextAction j A) (M.contextAction i (product D A)) := by
  let C' : M.PureObject := ⟨C⟩
  let D' : M.PureObject := ⟨D⟩
  let A' : M.PureObject := ⟨A⟩
  let ii : C' ⟶ D' ⊗ C' := ⟨i, hi⟩
  let jj : C' ⟶ C' ⊗ D' := ⟨j, hj⟩
  have hco' : jj ≫ ii ▷ D' ≫ (α_ D' C' D').hom = ii ≫ D' ◁ jj := Subtype.ext hco
  have h := congrArg Subtype.val (Structural.mixed_coaction ii jj hco' A')
  change M.compose (M.right i A)
    (M.compose (M.associator D C A) (M.left D (M.compose (M.right j A) (M.associator C D A)))) =
    M.compose (M.right j A) (M.compose (M.associator C D A)
      (M.compose (M.right i (product D A)) (M.associator D C (product D A)))) at h
  simpa only [contextAction, M.compose_assoc] using h

theorem contextAction_counit {C D : τ} (i : M.Hom C (product D C))
    (hi : M.hasEffect ⊥ i) (dD : Quantity.affine ≤ quantity D)
    (hco : M.compose i (M.compose (M.right (M.discard D dD) C) (M.leftUnitor C)) = M.identity C)
    (A : τ) :
    M.compose (M.contextAction i A)
      (M.compose (M.right (M.discard D dD) (product C A)) (M.leftUnitor (product C A))) =
      M.identity (product C A) := by
  let C' : M.PureObject := ⟨C⟩
  let D' : M.PureObject := ⟨D⟩
  let A' : M.PureObject := ⟨A⟩
  let ii : C' ⟶ D' ⊗ C' := ⟨i, hi⟩
  let dd : D' ⟶ 𝟙_ M.PureObject := ⟨M.discard D dD, M.discard_pure D dD⟩
  have hco' : ii ≫ dd ▷ C' ≫ (λ_ C').hom = 𝟙 C' := Subtype.ext hco
  have h := congrArg Subtype.val (Structural.left_coaction_counit ii dd hco' A')
  change M.compose (M.right i A) (M.compose (M.associator D C A)
    (M.compose (M.right (M.discard D dD) (product C A)) (M.leftUnitor (product C A)))) =
      M.identity (product C A) at h
  simpa only [contextAction, M.compose_assoc] using h

end SeqData
namespace Denotation
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

/-- A retained native split obeys left coassociativity. -/
theorem split_left_coassoc {n : Nat} {Γc Γl : QCtx τ n} (s : Γc.Split Γl Γc) :
    M.compose (split M.toSeqData s)
      (M.compose (M.right (M.copy (packed Γl) (s.relevant_retained.trans (packed_quantity Γl))) (packed Γc))
        (M.associator (packed Γl) (packed Γl) (packed Γc))) =
      M.compose (split M.toSeqData s) (M.left (packed Γl) (split M.toSeqData s)) := by
  have h := split_assoc M.toSeqData s (QCtx.Split.diagonal Γl s.relevant_retained) s s
  rw [split_diagonal M Γl s.relevant_retained] at h
  exact h

/-- The two orientations of a retained split commute. -/
theorem split_mixed_coassoc {n : Nat} {Γc Γl : QCtx τ n} (s : Γc.Split Γl Γc) :
    M.compose (split M.toSeqData s.symm)
      (M.compose (M.right (split M.toSeqData s) (packed Γl))
        (M.associator (packed Γl) (packed Γc) (packed Γl))) =
      M.compose (split M.toSeqData s) (M.left (packed Γl) (split M.toSeqData s.symm)) :=
  split_assoc M.toSeqData s.symm s s s.symm

/-- Discarding the supplied component of a retained split returns its source. -/
theorem split_left_counit {n : Nat} {Γc Γl : QCtx τ n} (s : Γc.Split Γl Γc) (hd : Γl.Discardable) :
    M.compose (split M.toSeqData s)
      (M.compose (M.right (discard M.toSeqData hd) (packed Γc)) (M.leftUnitor (packed Γc))) =
      M.identity (packed Γc) := by
  rw [split_weakenRight M s hd]
  exact weaken_refl M.toSeqData Γc

/-- A native retained split supplies a categorical right coaction, even when
its retained source contains linear resources. -/
def splitRightCoaction {n : Nat} {Γc Γl : QCtx τ n} (s : Γc.Split Γl Γc) (hd : Γl.Discardable) :
    M.toSeqData.RightCoaction (packed Γc) (packed Γl)
      (s.relevant_retained.trans (packed_quantity Γl)) (discardable_quantity hd) where
  map := split M.toSeqData s.symm
  pure := split_pure M.toSeqData s.symm
  coassoc := by
    have h := split_assoc M.toSeqData s.symm s.symm s.symm (QCtx.Split.diagonal Γl s.relevant_retained)
    rw [split_diagonal M Γl s.relevant_retained] at h
    exact h
  counit := by
    change M.compose (split M.toSeqData s.symm)
      (M.compose (M.left (packed Γc) (discard M.toSeqData hd)) (M.rightUnitor (packed Γc))) = _
    rw [split_weakenLeft M s.symm hd]
    exact weaken_refl M.toSeqData Γc

end Denotation
end Silmaril.Isotope.Refinement.Models
