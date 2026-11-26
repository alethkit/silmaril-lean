module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Defs

/-! # Guarded iteration and a conditional strong Elgot Freyd structure -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open CategoryTheory CategoryTheory.Limits

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Comp" => Paper.WithCaseReturns.TypeCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "inc" => inclusion (τ := τ) (Φ := Φ) pe

attribute [local instance] valueCartesian valueBraided computationPremonoidal computationSymmetric
  computationDistributive valueDistributive guardedIteration

/-- The installed guarded feedback operator satisfies the three Elgot equations. -/
theorem computationElgot : ElgotCategory Comp :=
  Extension.Singleton.guardedElgot Seed

attribute [local instance] computationElgot

/-- Supply the strong Elgot Freyd structure once the actual structural-state uniformity field is given. -/
@[expose, instance_reducible]
noncomputable def strongElgotOfUniformity (uniformity : StructuralUniformity (τ := τ) (Φ := Φ) pe) :
    StrongElgotFreydCategory (inc) where
  toElgotFreydCategory := {
    toDistributiveFreydCategory := distributiveFreyd pe
    uniformity := uniformity }
  iterate_whiskerLeft Z f := iterate_whiskerLeft pe Z f

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues
