module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iso.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Thms

/-! # Exact-sum iteration under the ordered-pair singleton comparisons -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton

open CategoryTheory
open Paper.Extension.Singleton (ofType ofRegion iterateSum_map)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "G" => ofType (Φ := Φ) Seed

variable {A B : τ}

open SyntacticCategory (iterateRegion iterateRegion_valueBranches)

/-- Build the literal feedback CFG after binding the step's branch arguments. -/
def iterateRep (r : Rep (Φ := Φ) A (coprod B A)) : Rep (Φ := Φ) A B :=
  ⟨iterateRegion A r.val.bindBranchArguments, (iterateRegion_valueBranches r.property.bindBranchArguments).hasType⟩

theorem normalize_iterateRep (r : Rep (Φ := Φ) A (coprod B A)) :
    normalizeHom pe (Quotient.mk _ (iterateRep r)) = Extension.Singleton.iterateSum Seed
      (normalizeHom pe (Quotient.mk _ r)) := by
  change normalizeHom pe (rawClass pe (iterateRegion_valueBranches r.property.bindBranchArguments).hasType) =
    Extension.Singleton.iterateSum Seed (ofRegion Seed r.property.bindBranchArguments)
  rw [normalize_guarded, iterateSum_map, Paper.TypeCategory.iterateSum_ofRegion]

/-- Descend the literal representative operation to the raw exact-sum quotient. -/
def iterateSum (f : RawHom (Φ := Φ) pe A (coprod B A)) : RawHom (Φ := Φ) pe A B :=
  Quotient.map iterateRep (fun r s h => Quotient.exact
    (normalizeHom_injective pe (by
      rw [normalize_iterateRep, normalize_iterateRep, congrArg (normalizeHom pe) (Quotient.sound h)]))) f

theorem normalize_iterateSum (f : RawHom (Φ := Φ) pe A (coprod B A)) :
    normalizeHom pe (iterateSum pe f) = Extension.Singleton.iterateSum Seed (normalizeHom pe f) :=
  Quotient.inductionOn f (normalize_iterateRep pe)

local notation "Added" => AddBinding Seed

theorem addBinding_iterateSum {f : G A ⟶ G (coprod B A)} :
    (addBindingFunctor pe).map (Extension.Singleton.iterateSum Seed f) =
      Extension.Singleton.iterateSum Added ((addBindingFunctor pe).map f) := by
  induction f using Quot.ind with
  | _ f => rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton
