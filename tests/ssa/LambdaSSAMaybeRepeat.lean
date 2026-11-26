module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Repeat.Thms
import Silmaril.Semantics.ITree.Thms

open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit
open scoped Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit
open CategoryTheory

example (capture state : Bits) :
    (identityRepeatStep ≫ (Kleisli.Type.coprodIsoSum MaybeT (J.obj Carried) (J.obj Carried)).hom).of
      (stateInput capture state) = Sum.inl (Sum.inr (stateInput capture state)) := by
  rw [identityRepeatStep_eq, Kleisli.Type.inr_coprodIsoSum_hom]
  rfl

example (capture state : Bits) :
    (CategoryTheory.iterate identityRepeatStep).of (stateInput capture state) = Sum.inr PUnit.unit :=
  identityRepeat_iterate_apply _

open Silmaril.Elgot.ITree

/-- With no return type, the first visible instruction still separates the
infinite call loop from the silent identity loop. -/
example {E : Type → Type} {R : Type} (event : E R) :
    Silmaril.Elgot.iter (fun s : PUnit => vis event (fun _ => pure (Sum.inr s)) :
      PUnit → Tree E (PEmpty ⊕ PUnit)) PUnit.unit ≠
      Silmaril.Elgot.iter (fun s : PUnit => (pure (Sum.inr s) : Tree E (PEmpty ⊕ PUnit))) PUnit.unit := by
  let step : PUnit → Tree E (PEmpty ⊕ PUnit) := fun s => vis event (fun _ => pure (Sum.inr s))
  change Silmaril.Elgot.iter step PUnit.unit ≠ _
  rw [iterate_forever]
  intro equal
  have fixed : Silmaril.Elgot.iter step PUnit.unit =
      vis event (fun _ => Silmaril.Elgot.iter step PUnit.unit) := by
    simpa only [step, vis_bind, pure_bind, Sum.elim_inr] using
      congrFun (iterate_fixpoint step) PUnit.unit
  rw [equal] at fixed
  have observation := congrArg out fixed
  rw [out_diverge, out_vis] at observation
  exact Part.some_ne_none _ observation.symm
