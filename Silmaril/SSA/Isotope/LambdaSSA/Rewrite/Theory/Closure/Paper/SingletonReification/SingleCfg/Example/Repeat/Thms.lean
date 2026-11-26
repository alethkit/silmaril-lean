module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Repeat.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Interpretation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MaybeIdentityRepeat

/-! # The actual repeat block and the joined empty-exit image in Maybe -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory CapturedRecurExit
open Paper.Extension.Singleton (ofType ofRegion emptyIsInitial)
open Paper.WithProjectionReturnsAndUnitEta.Reification (canonicalIterate)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (denoteSingletonRegion)

local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Empty) (Φ := Empty)
local notation "Obj" => ofType (Seed)
local notation "Zero" => Obj (Ty.empty : Ty Empty)

/-- On a typed representative the local Maybe map is the actual singleton denotation. -/
theorem denoteJoinedEmpty_ofRegion {A : Ty Empty} {r : Region Empty}
    (hr : ValueBranches [A] r [.empty]) :
    denoteJoinedEmpty A (ofRegion (Seed) hr) = denoteSingletonRegion J M hr.hasType :=
  @Subsingleton.elim _ (maybeEmpty_hom (M.obj A)) _ _

/-- The selected Maybe arrow agrees with the interpreted guarded arrow into
the empty type, in particular for input type unit. -/
theorem selectedRepeatEmpty_agrees (A : Ty Empty) :
    CategoryTheory.iterate (coprod.inr : J.obj (M.obj A) ⟶ J.obj (M.obj .empty) ⨿ J.obj (M.obj A)) =
      denoteJoinedEmpty A (canonicalIterate (coprod.inr : Obj A ⟶ Zero ⨿ Obj A)) :=
  @Subsingleton.elim _ (maybeEmpty_hom (M.obj A)) _ _

/-- The guarded repeat-result arrow is its selected empty-exit arrow followed
by the unique outward map in the joined quotient. -/
theorem guardedRepeat_factorsThroughEmpty (A B : Ty Empty) :
    canonicalIterate (coprod.inr : Obj A ⟶ Obj B ⨿ Obj A) =
      canonicalIterate (coprod.inr : Obj A ⟶ Zero ⨿ Obj A) ≫ (emptyIsInitial (Seed)).to (Obj B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MaybeIdentityRepeat.guardedRepeat_factorsThroughEmpty A B

/-- The actual block repeats with exactly the incoming carrier. -/
theorem identityRepeatStep_eq : identityRepeatStep = coprod.inr :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MaybeIdentityRepeat.identityRepeatStep_eq

/-- The actual repeat-only loop in Maybe produces no result. -/
theorem identityRepeat_iterate_apply (input : Carried) :
    (CategoryTheory.iterate identityRepeatStep).of input = (Sum.inr PUnit.unit : MaybeT Carried) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MaybeIdentityRepeat.identityRepeat_iterate_apply input

/-- In packed coordinates the actual loop equals the Maybe interpretation
of the guarded empty-exit arrow followed by the interpreted outward map. -/
theorem identityRepeat_repacked_eq_image :
    J.map (carriedIso M Flag Flag).inv ≫ CategoryTheory.iterate identityRepeatStep ≫
      J.map (carriedIso M Flag Flag).hom =
        denoteJoinedEmpty Carry (canonicalIterate (coprod.inr : Obj Carry ⟶ Zero ⨿ Obj Carry)) ≫
          J.map (M.emptyIsInitial.to (M.obj Carry)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MaybeIdentityRepeat.identityRepeat_repacked_eq_image

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit
