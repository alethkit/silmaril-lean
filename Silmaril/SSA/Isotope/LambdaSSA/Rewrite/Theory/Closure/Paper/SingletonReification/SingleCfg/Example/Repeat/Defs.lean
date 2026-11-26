module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Interpretation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Divergence.Defs

/-! # The empty-exit interpretation of the pure repeat block in Maybe -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory CapturedRecurExit
open Paper.Extension.Singleton (ofType denoteSubsingleton)
open Paper.WithProjectionReturnsAndUnitEta.Reification (repeatStateBlock)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (denoteSingletonRegion)
open Silmaril.Isotope.LetIter.Semantics.Categorical (contextualStep)

local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Empty) (Φ := Empty)
local notation "Obj" => ofType (Seed)

/-- At the empty result type, Maybe has only its no-result value. -/
theorem maybeEmpty_value (x : MaybeT PEmpty) : x = .inr PUnit.unit := by
  cases x with
  | inl e => exact e.elim
  | inr u => cases u; rfl

/-- Every computation into the interpreted empty type has the same result. -/
theorem maybeEmpty_hom (A : Type) : Subsingleton (J.obj A ⟶ J.obj PEmpty) :=
  ⟨fun f g => Kleisli.hom_ext (ConcreteCategory.coe_ext (funext fun a =>
    (maybeEmpty_value (f.of a)).trans (maybeEmpty_value (g.of a)).symm))⟩

/-- Interpret the descended joined arrow at the empty exit by its typed
singleton denotation in the existing Maybe model. -/
noncomputable def denoteJoinedEmpty (A : Ty Empty) (f : Obj A ⟶ Obj (.empty : Ty Empty)) :
    J.obj (M.obj A) ⟶ J.obj (M.obj .empty) :=
  letI : Subsingleton (J.obj (M.obj A) ⟶ J.obj (M.obj .empty)) := maybeEmpty_hom (M.obj A)
  denoteSubsingleton (Seed) J M f

/-- The actual contextual step of the pure repeat block on the example carrier. -/
noncomputable abbrev identityRepeatStep : J.obj Carried ⟶ J.obj Carried ⨿ J.obj Carried :=
  contextualStep J (blockComputation M J Flag Flag Flag
    (denoteSingletonRegion J M (repeatStateBlock (Φ := Empty) Flag Flag Flag).hasType))

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit
