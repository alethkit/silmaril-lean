module

public import Silmaril.Semantics.Calco2019.Parametrized
public import Silmaril.Semantics.Calco2019.ResumptionThms

/-! # Guarded resumption maps and their iteration -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (M : ParametrizedGuardedElgotMonad P) (R : FinalResumptions M.toParametrizedMonad)

namespace ParametrizedGuardedElgotMonad

/-- Guardedness in the Kleisli category at a particular parameter. -/
abbrev guardedAt (W : C) {X Y Z : C} (f : X ⟶ (M.obj W).monad.obj (P.sum Y Z)) : Prop :=
  (M.obj W).guard.guarded
    (Y := Kleisli.mk (M.obj W).monad Y) (Z := Kleisli.mk (M.obj W).monad Z) (kleisliArrow f)

/-- Definition 24. A resumption map is guarded when its first observation is guarded. -/
def ResumptionGuard {X Y Z : C} (f : X ⟶ R.obj (P.sum Y Z)) : Prop :=
  M.guardedAt (R.obj (P.sum Y Z)) (Y := Y) (Z := Z) (f ≫ R.out (P.sum Y Z))

/-- Definition 24 as a predicate on the resumption Kleisli category. -/
abbrev observedGuard {X Y Z : Kleisli (R.monad P)}
    (f : X ⟶ (P.kleisli (R.monad P)).sum Y Z) : Prop :=
  M.ResumptionGuard R (X := X.of) (Y := Y.of) (Z := Z.of) f.of

/-- Both nested recursive summands are guarded after pure reassociation. -/
def ResumptionNested {S X Y Z : C} (f : S ⟶ R.obj (P.sum (P.sum X Y) Z)) : Prop :=
  M.ResumptionGuard R (Y := X) (Z := P.sum Y Z) (f ≫ (R.monad P).map P.assoc)

/-- The inner iteration `♦ f` of Theorem 25, in the monad at the fixed resumption parameter. -/
def diamond {X Y : C} (f : X ⟶ R.obj (P.sum Y X)) (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    X ⟶ (M.obj (R.obj (P.sum Y X))).monad.obj Y :=
  ((M.obj (R.obj (P.sum Y X))).iteration.iterate
    (kleisliArrow (f ≫ R.out (P.sum Y X))) hf).of

/-- The solution obtained by first iterating immediate recursive calls and then using finality. -/
def iterateResumption {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) : X ⟶ R.obj Y :=
  R.solve P (M.diamond R f hf)

/-- Postprocess a successful return and keep recursive calls in the right summand. -/
def naturalityBody {X Y Z : C} (f : X ⟶ R.obj (P.sum Y X)) (g : Y ⟶ R.obj Z) :
    X ⟶ R.obj (P.sum Z X) :=
  f ≫ R.extend P (P.desc (g ≫ (R.monad P).map P.inl) (P.inr ≫ R.unit (P.sum Z X)))

end ParametrizedGuardedElgotMonad
end Silmaril.Calco2019
