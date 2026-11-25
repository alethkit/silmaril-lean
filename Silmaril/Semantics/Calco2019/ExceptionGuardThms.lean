module

public import Silmaril.Semantics.Calco2019.ExceptionGuard
import Silmaril.Proofs.Semantics.Calco2019.ExceptionGuard

/-! # Guards and chosen fixpoints at an exception parameter -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C} (T : GuardedElgotMonad P)

theorem guard_trivial (E : C) {X Y Z : Kleisli ((family P T.monad).obj E)} (f : X ⟶ Y) :
    kleisliGuard P T E (f ≫ (P.kleisli ((family P T.monad).obj E)).inl (Y := Z)) :=
  Proofs.exception_guard_trivial T E f

theorem guard_parallel (E : C) {X X' Y Z : Kleisli ((family P T.monad).obj E)}
    {f : X ⟶ (P.kleisli ((family P T.monad).obj E)).sum Y Z}
    {g : X' ⟶ (P.kleisli ((family P T.monad).obj E)).sum Y Z}
    (hf : kleisliGuard P T E (Y := Y) (Z := Z) f) (hg : kleisliGuard P T E (Y := Y) (Z := Z) g) :
    kleisliGuard P T E (Y := Y) (Z := Z) ((P.kleisli ((family P T.monad).obj E)).desc f g) :=
  Proofs.exception_guard_parallel T E hf hg

theorem guard_compose (E : C) {X Y Z V W : Kleisli ((family P T.monad).obj E)}
    {f : X ⟶ (P.kleisli ((family P T.monad).obj E)).sum Y Z}
    {g : Y ⟶ (P.kleisli ((family P T.monad).obj E)).sum V W}
    (h : Z ⟶ (P.kleisli ((family P T.monad).obj E)).sum V W)
    (hf : kleisliGuard P T E (Y := Y) (Z := Z) f) (hg : kleisliGuard P T E (Y := V) (Z := W) g) :
    kleisliGuard P T E (Y := V) (Z := W) (f ≫ (P.kleisli ((family P T.monad).obj E)).desc g h) :=
  Proofs.exception_guard_compose T E h hf hg

/-- The rearrangement described in Example 22 obeys the three guard axioms. -/
@[expose]
def guardedness (E : C) : MonadGuardedness P ((family P T.monad).obj E) where
  guarded f := kleisliGuard P T E f
  trivial f := guard_trivial T E f
  parallel hf hg := guard_parallel T E hf hg
  compose h hf hg := guard_compose T E h hf hg

theorem fixpoint (E : C) {X Y : Kleisli ((family P T.monad).obj E)}
    (f : X ⟶ (P.kleisli ((family P T.monad).obj E)).sum Y X)
    (hf : kleisliGuard P T E (Y := Y) (Z := X) f) :
    Guardedness.IsFixpoint f (kleisliArrow (iterate P T E f.of hf)) :=
  Proofs.exception_fixpoint T E f hf

/-- Guarded loops use the base fixpoint after moving exceptions to the return summand. -/
@[expose]
def fixpoints (E : C) : (guardedness T E).Fixpoints where
  iterate f hf := kleisliArrow (iterate P T E f.of hf)
  fixpoint f hf := fixpoint T E f hf

theorem change_guard {E E' X Y Z : C} (h : E ⟶ E')
    {f : X ⟶ T.monad.obj (P.sum (P.sum Y Z) E)} (hf : Guard P T E (Y := Y) (Z := Z) f) :
    Guard P T E' (Y := Y) (Z := Z) (f ≫ changeException P T.monad h (P.sum Y Z)) :=
  Proofs.change_guard T E h hf

theorem change_preserves {E E' : C} (h : E ⟶ E') :
    MonadGuardedness.Preserves P (guardedness T E) (guardedness T E') ((family P T.monad).map h) :=
  fun _ hf => change_guard T h hf

/-- Parameter maps preserve the selected solutions as well as their guards. -/
theorem change_iterate {E E' X Y : C} (h : E ⟶ E')
    {f : X ⟶ T.monad.obj (P.sum (P.sum Y X) E)} (hf : Guard P T E (Y := Y) (Z := X) f) :
    iterate P T E f hf ≫ changeException P T.monad h Y =
      iterate P T E' (f ≫ changeException P T.monad h (P.sum Y X)) (change_guard T h hf) :=
  Proofs.change_iterate T E h hf

end Silmaril.Calco2019.Exception
