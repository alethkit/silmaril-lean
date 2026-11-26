module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Substitution

/-! # Value environment maps for exact binder renaming -/

public section

universe u v w h

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {V : Type v} [Category.{h} V]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V] (M : TypeModel τ V)
  {ν : Type w} {Γ : Ctx ν τ} {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}

/-- Bound renaming leaves the free component of the environment alone. -/
theorem envRenameMap_free (ρ : BoundCtx.Renaming β δ) :
    envRenameMap M Γ ρ ≫ fst _ _ = fst _ _ :=
  envRenameMap_free_proof M ρ

/-- The renamed environment reads the corresponding typed bound slot. -/
theorem envRenameMap_bound (ρ : BoundCtx.Renaming β δ) (i : Fin n) :
    envRenameMap M Γ ρ ≫ boundVar M i =
      boundVar M (Γ := Γ) (ρ.toFun i) ≫ eqToHom (congrArg M.obj (ρ.typed i)) :=
  envRenameMap_bound_proof M ρ i

/-- Under one binder, rename the old slots and retain the new value. -/
theorem envRenameMap_snoc (ρ : BoundCtx.Renaming β δ) (A : τ) :
    (envSnocIso M Γ δ A).hom ≫ envRenameMap M Γ (ρ.up A) =
      (envRenameMap M Γ ρ ▷ M.obj A) ≫ (envSnocIso M Γ β A).hom :=
  envRenameMap_snoc_proof M ρ A

/-- Under a product binder, rename the old slots and retain both components. -/
theorem envRenameMap_pair (ρ : BoundCtx.Renaming β δ) (A B : τ) :
    envPairHom M Γ δ A B ≫ envRenameMap M Γ ((ρ.up A).up B) =
      (envRenameMap M Γ ρ ▷ (M.obj A ⊗ M.obj B)) ≫ envPairHom M Γ β A B :=
  envRenameMap_pair_proof M ρ A B

/-- Inserting a slot below the newest binder drops exactly that slot. -/
theorem envRenameMap_underBinder (X Y : τ) :
    (envSnocIso M Γ (β.snoc X) Y).hom ≫
        envRenameMap M Γ (BoundCtx.Renaming.underBinder β X Y) =
      (dropSlot M β X ▷ M.obj Y) ≫ (envSnocIso M Γ β Y).hom :=
  envRenameMap_underBinder_proof M X Y

end Silmaril.Isotope.LetIter.Semantics.Categorical
