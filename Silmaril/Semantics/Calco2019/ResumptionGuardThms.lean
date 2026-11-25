module

public import Silmaril.Semantics.Calco2019.ResumptionGuard
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

/-! # Guardedness and the resumption fixpoint equation -/

public section

universe u v

namespace Silmaril.Calco2019.ParametrizedGuardedElgotMonad

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (M : ParametrizedGuardedElgotMonad P) (R : FinalResumptions M.toParametrizedMonad)

/-- The inherited guardedness of the resumption monad, with the axioms of Definition 6. -/
def resumptionGuardedness : MonadGuardedness P (R.monad P) where
  guarded f := M.observedGuard R f
  trivial f := Proofs.observedGuard_trivial M R f
  parallel hf hg := Proofs.observedGuard_parallel M R hf hg
  compose h hf hg := Proofs.observedGuard_compose M R h hf hg

theorem resumptionGuardedness_iff {X Y Z : Kleisli (R.monad P)}
    (f : X ⟶ (P.kleisli (R.monad P)).sum Y Z) :
    (M.resumptionGuardedness R).guarded f ↔
      M.ResumptionGuard R (Y := Y.of) (Z := Z.of) f.of :=
  Iff.rfl

theorem resumptionGuardedness_total (h : ∀ W : C, (M.obj W).IsElgot)
    {X Y Z : Kleisli (R.monad P)} (f : X ⟶ (P.kleisli (R.monad P)).sum Y Z) :
    (M.resumptionGuardedness R).guarded f :=
  (M.resumptionGuardedness_iff R f).mpr
    (h (R.obj (P.sum Y.of Z.of))
      (Y := Kleisli.mk (M.obj _).monad Y.of) (Z := Kleisli.mk (M.obj _).monad Z.of)
      (kleisliArrow (f.of ≫ R.out (P.sum Y.of Z.of))))

/-- The observation equation characterizes the two-stage iteration uniquely. -/
theorem iterateResumption_characterization {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    R.IsSolution P (M.diamond R f hf) (M.iterateResumption R f hf) ∧
      ∀ g, R.IsSolution P (M.diamond R f hf) g → g = M.iterateResumption R f hf :=
  ⟨R.solve_spec P _, fun g hg => R.solve_unique P _ g hg⟩

/-- The two-stage iteration solves the original recursive equation in the resumption monad. -/
theorem iterateResumption_fixpoint {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    f ≫ R.extend P (P.desc (R.unit Y) (M.iterateResumption R f hf)) =
      M.iterateResumption R f hf :=
  Proofs.iterateResumption_fixpoint M R f hf

end Silmaril.Calco2019.ParametrizedGuardedElgotMonad
