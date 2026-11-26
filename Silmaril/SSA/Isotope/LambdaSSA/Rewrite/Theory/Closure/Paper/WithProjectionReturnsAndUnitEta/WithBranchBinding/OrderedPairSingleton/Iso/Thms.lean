module

public import Mathlib.CategoryTheory.Category.Cat
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Thms

/-! # Strict isomorphisms for the ordered-pair singleton quotients -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton

open CategoryTheory
open Paper.Extension.Singleton (ofType ofRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Guarded" => Extension.Singleton.TypeCategory Seed

variable {A B : τ}

local notation "HomE" => homEquiv (τ := τ) (Φ := Φ) pe

local notation "G" => ofType (Φ := Φ) Seed

noncomputable def toRawHom (f : G A ⟶ G B) : RawHom (Φ := Φ) pe A B :=
  (HomE A B).symm f

@[simp] theorem normalize_toRawHom (f : G A ⟶ G B) :
    normalizeHom pe (toRawHom pe f) = f :=
  (HomE A B).apply_symm_apply f

noncomputable def toRawFunctor : Guarded ⥤ RawTypeCategory (τ := τ) Φ pe where
  obj X := ⟨X.as⟩
  map := toRawHom pe
  map_id X := normalizeHom_injective pe
    ((normalize_toRawHom pe (𝟙 X)).trans (normalize_identity pe).symm)
  map_comp f g := normalizeHom_injective pe
    ((normalize_toRawHom pe (f ≫ g)).trans
      ((normalize_compose pe (toRawHom pe f) (toRawHom pe g)).trans
        (congrArg₂ CategoryStruct.comp (normalize_toRawHom pe f) (normalize_toRawHom pe g))).symm)

/-- The inverse includes any guarded representative into the raw quotient. -/
theorem toRaw_ofRegion {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    (toRawFunctor pe).map (ofRegion Seed hr) = rawClass pe hr.hasType :=
  (HomE A B).symm_apply_eq.mpr (normalize_guarded pe hr).symm

/-- The raw branch-binding category and the existing guarded quotient are strictly isomorphic. -/
noncomputable def categoryIso : Cat.of (RawTypeCategory (τ := τ) Φ pe) ≅ Cat.of Guarded where
  hom := (normalizeFunctor pe).toCatHom
  inv := (toRawFunctor pe).toCatHom
  hom_inv_id := by
    apply Cat.ext
    change normalizeFunctor pe ⋙ toRawFunctor pe = 𝟭 _
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun X Y f => ?_)
    exact heq_of_eq ((HomE X.as Y.as).symm_apply_apply f)
  inv_hom_id := by
    apply Cat.ext
    change toRawFunctor pe ⋙ normalizeFunctor pe = 𝟭 _
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun X Y f => ?_)
    exact heq_of_eq ((HomE X.as Y.as).apply_symm_apply f)

local notation "Added" => AddBinding Seed
local notation "Expanded" => Extension.Singleton.TypeCategory Added
local notation "P" => Paper.Extension.Singleton.projection

theorem guardedHomRel_iff {X Y : Paper.TypeCategory (τ := τ) Φ} {f g : X ⟶ Y} :
    Extension.Singleton.homRel Added f g ↔ Extension.Singleton.homRel Seed f g := by
  constructor
  · rintro ⟨r, s, hr, hs, ef, eg, eqv⟩
    exact ⟨r, s, hr, hs, ef, eg, (pairJoined_guarded_eqv_iff hr hs).mp eqv⟩
  · rintro ⟨r, s, hr, hs, ef, eg, eqv⟩
    exact ⟨r, s, hr, hs, ef, eg, ofSeed eqv⟩

def addBindingFunctor : Guarded ⥤ Expanded :=
  CategoryTheory.Quotient.lift (Extension.Singleton.homRel Seed) (P Added) fun _ _ _ _ h =>
    CategoryTheory.Quotient.sound _ ((guardedHomRel_iff pe).mpr h)

def removeBindingFunctor : Expanded ⥤ Guarded :=
  CategoryTheory.Quotient.lift (Extension.Singleton.homRel Added) (P Seed) fun _ _ _ _ h =>
    CategoryTheory.Quotient.sound _ ((guardedHomRel_iff pe).mp h)

/-- The two existing guarded quotient categories also have strictly inverse projections. -/
def guardedCategoryIso : Cat.of Guarded ≅ Cat.of Expanded where
  hom := (addBindingFunctor pe).toCatHom
  inv := (removeBindingFunctor pe).toCatHom
  hom_inv_id := by
    apply Cat.ext
    change addBindingFunctor pe ⋙ removeBindingFunctor pe = 𝟭 _
    apply CategoryTheory.Quotient.lift_unique'
    rfl
  inv_hom_id := by
    apply Cat.ext
    change removeBindingFunctor pe ⋙ addBindingFunctor pe = 𝟭 _
    apply CategoryTheory.Quotient.lift_unique'
    rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton
