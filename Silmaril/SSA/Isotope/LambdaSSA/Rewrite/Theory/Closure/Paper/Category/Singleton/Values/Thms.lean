module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PureReturnComposition

/-! # Composition of pure returns and their two interchange squares -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

theorem returnTerm_id (A : τ) :
    returnTerm (Φ := Φ) (.var (i := 0) (show At [A] 0 A from rfl)) = 𝟙 (ofType A) :=
  PureReturnComposition.returnTerm_id A

/-- Unary let sequences two singleton returns after weakening the second to admit the original input. -/
theorem returnTerm_comp {A B C : τ} {a b : Tm Φ}
    (ha : Tm.HasType [A] a B) (hb : Tm.HasType [B] b C) :
    returnTerm ha ≫ returnTerm hb =
      returnTerm (.let₁ ha (hb.rename ((Ren.wk [] A).lift B))) :=
  PureReturnComposition.returnTerm_comp ha hb

/-- A constructor argument can be returned before the primitive consumes it. -/
theorem returnTerm_op_branchValue {A : τ} {a : Tm Φ} (f : Φ)
    (ha : Tm.BranchValue [A] a (instrSrc f)) :
    returnTerm (.op (f := f) ha.hasType) = returnTerm ha.hasType ≫ primitiveReturn f :=
  PureReturnComposition.returnTerm_op_branchValue f ha

/-- Composition in the left factor uses only right-whiskering functoriality. -/
theorem interchange_left_comp {A B C X Y : Comp} {f : A ⟶ B} {g : B ⟶ C} {k : X ⟶ Y}
    (hf : whiskerRight f X ≫ whiskerLeft B k = whiskerLeft A k ≫ whiskerRight f Y)
    (hg : whiskerRight g X ≫ whiskerLeft C k = whiskerLeft B k ≫ whiskerRight g Y) :
    whiskerRight (f ≫ g) X ≫ whiskerLeft C k =
      whiskerLeft A k ≫ whiskerRight (f ≫ g) Y :=
  PureReturnComposition.interchange_left_comp hf hg

/-- Composition in the right factor uses only left-whiskering functoriality. -/
theorem interchange_right_comp {A B C X Y : Comp} {f : A ⟶ B} {g : B ⟶ C} {k : X ⟶ Y}
    (hf : whiskerLeft X f ≫ whiskerRight k B = whiskerRight k A ≫ whiskerLeft Y f)
    (hg : whiskerLeft X g ≫ whiskerRight k C = whiskerRight k B ≫ whiskerLeft Y g) :
    whiskerLeft X (f ≫ g) ≫ whiskerRight k C =
      whiskerRight k A ≫ whiskerLeft Y (f ≫ g) :=
  PureReturnComposition.interchange_right_comp hf hg

theorem WhiskerCentral.id (A : Comp) : WhiskerCentral (𝟙 A) := by
  intro X Y k
  exact ⟨by rw [whiskerRight_id, whiskerRight_id, Category.id_comp, Category.comp_id],
    by rw [whiskerLeft_id, whiskerLeft_id, Category.id_comp, Category.comp_id]⟩

theorem WhiskerCentral.comp {A B C : Comp} {f : A ⟶ B} {g : B ⟶ C}
    (hf : WhiskerCentral f) (hg : WhiskerCentral g) : WhiskerCentral (f ≫ g) :=
  fun {_ _} k => ⟨interchange_left_comp (hf k).1 (hg k).1, interchange_right_comp (hf k).2 (hg k).2⟩

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

theorem pureReturn_returnTerm {A B : τ} {a : Tm Φ} (ha : Tm.HasType [A] a B) (hp : Tm.Pure pe a) :
    PureReturn pe (returnTerm ha) :=
  ⟨a, ha, hp, rfl⟩

theorem pureReturn_id (A : Comp) : PureReturn pe (𝟙 A) :=
  ⟨.var 0, .var rfl, .var, (returnTerm_id (show τ from A)).symm⟩

theorem pureReturn_comp {A B C : Comp} {f : A ⟶ B} {g : B ⟶ C}
    (hf : PureReturn pe f) (hg : PureReturn pe g) : PureReturn pe (f ≫ g) := by
  obtain ⟨_, ha, pa, rfl⟩ := hf
  obtain ⟨_, hb, pb, rfl⟩ := hg
  exact ⟨_, .let₁ ha (hb.rename ((Ren.wk [] (show τ from A)).lift (show τ from B))),
    .let₁ pa (pb.rename (Silmaril.DeBruijn.lift Nat.succ)), returnTerm_comp ha hb⟩

instance pureReturn_multiplicative : (PureReturn (τ := τ) (Φ := Φ) pe).IsMultiplicative where
  id_mem := pureReturn_id pe
  comp_mem _ _ := pureReturn_comp pe

instance centralPureReturn_multiplicative : (CentralPureReturn (τ := τ) (Φ := Φ) pe).IsMultiplicative where
  id_mem A := ⟨pureReturn_id pe A, WhiskerCentral.id A⟩
  comp_mem _ _ hf hg := ⟨pureReturn_comp pe hf.1 hg.1, WhiskerCentral.comp hf.2 hg.2⟩

/-- A unary let sequencing two central pure singletons is again a central pure return. -/
theorem centralPureReturn_let {A B C : τ} {a b : Tm Φ}
    (ha : Tm.HasType [A] a B) (hb : Tm.HasType [B] b C)
    (h₁ : CentralPureReturn pe (returnTerm ha)) (h₂ : CentralPureReturn pe (returnTerm hb)) :
    CentralPureReturn pe (returnTerm (.let₁ ha (hb.rename ((Ren.wk [] A).lift B)))) :=
  (returnTerm_comp ha hb) ▸ (CentralPureReturn pe).comp_mem _ _ h₁ h₂

/-- The wide category of pure returns whose interchange squares hold. -/
abbrev CentralValueCategory := WideSubcategory (CentralPureReturn (τ := τ) (Φ := Φ) pe)

/-- Include certified central pure returns into the computation category. -/
abbrev centralValues : CentralValueCategory (τ := τ) (Φ := Φ) pe ⥤ Comp :=
  wideSubcategoryInclusion _

instance centralValues_faithful : (centralValues (τ := τ) (Φ := Φ) pe).Faithful :=
  inferInstanceAs (wideSubcategoryInclusion _).Faithful

/-- Primitive interchange is precisely what is needed for the constructor-and-primitive generators
and their finite sequential composites. -/
theorem primitiveReturnsCentral_iff_generated :
    PrimitiveReturnsCentral (τ := τ) (Φ := Φ) pe ↔
      (PureReturnGenerators (τ := τ) (Φ := Φ) pe).multiplicativeClosure ≤ CentralPureReturn pe := by
  constructor
  · intro h
    exact (MorphismProperty.multiplicativeClosure_le_iff _ _).mpr
      (PureReturnComposition.pureReturnGenerators_le pe h)
  · intro h f hp
    exact (h _ (.of _ (.inr ⟨f, .op (.var rfl), hp, rfl⟩))).2

/-- A pure primitive applied to a constructor value has both interchange squares under
the primitive law. -/
theorem centralPureReturn_op_branchValue {A : τ} {a : Tm Φ} (f : Φ) (hf : IsPure pe f)
    (ha : Tm.BranchValue [A] a (instrSrc f))
    (central : PrimitiveReturnsCentral (τ := τ) (Φ := Φ) pe) :
    CentralPureReturn pe (returnTerm (.op (f := f) ha.hasType)) := by
  rw [returnTerm_op_branchValue f ha]
  have h := PureReturnComposition.pureReturnGenerators_le pe central
  exact (CentralPureReturn pe).comp_mem _ _ (h _ (.inl ⟨a, ha, rfl⟩))
    (h _ (.inr ⟨f, .op (.var rfl), hf, rfl⟩))

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
