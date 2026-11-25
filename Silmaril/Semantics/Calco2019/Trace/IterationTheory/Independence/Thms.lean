module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Independence.Defs
public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.PointedModel.Thms
public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Independence.Thms
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationIndependence

/-! # The binary cycle instance and independence of the commutative schema -/

public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits Guardedness IterationTheory

/-- On the copower generator, the binary cycle identity is an instance of
the finite surjective commutative schema. -/
theorem IterationTheory.FiniteCopowers.binaryCycle_of_commutative
    {K : Type u} [Category.{v} K] {P : Coproducts K} {X Y : K}
    (C : FiniteCopowers X) (F : (greatest P).Conway) (comm : C.CommutativeIdentities F.toFixpoints)
    (f : X ⟶ P.sum Y X) :
    F.iterate (binaryCycleBody f) True.intro =
      P.desc (𝟙 X) (𝟙 X) ≫ F.iterate f True.intro :=
  Proofs.IterationIndependence.binary_of_commutative C F comm f

/-- The same categorical equation holds for least-fixed-point iteration in
every pointed ω-cpo, with arbitrary parameter objects and bodies. -/
theorem IterationTheory.PointedModel.binaryCycleIdentity :
    (PointedModel.conway.{u}).toFixpoints.BinaryCycleIdentity :=
  Fixpoints.binaryCycleIdentity_of_fold PointedModel.structural_uniformity.fold

namespace CounterSemiring.FiniteMatrix

theorem copower_has_colimit (X : Object.{u}) (I : Type) [Finite I] :
    Nonempty (IsColimit (copowerCofan X I)) :=
  Proofs.IterationIndependence.matrix_copower X I

/-- Chosen finite copowers for every generator in the finite matrix category. -/
noncomputable def copowers (X : Object.{u}) : FiniteCopowers X where
  cofan := copowerCofan X
  colimit I := Classical.choice (copower_has_colimit X I)

/-- The full Conway equations hold in the finite matrix category, but its
operator fails the finite commutative schema on copowers of one state. -/
theorem conway_fails_commutative :
    ¬ (copowers one).CommutativeIdentities conway.toFixpoints :=
  fun h => oneBody_fails_binaryCycle ((copowers one).binaryCycle_of_commutative conway h oneBody)

end CounterSemiring.FiniteMatrix

end Silmaril.Calco2019
