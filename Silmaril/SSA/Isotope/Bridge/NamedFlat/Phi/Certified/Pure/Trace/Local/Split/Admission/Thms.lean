module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction (Primitive)

section Captures

universe u
variable {V W K J Base : Type u} {n : Nat}
  {plan : Plan V W K J} {names : Fin n → Option V} {β : BoundCtx (Ty Base) n}

/-- Every old capture position has the same type in the extended context. -/
def originalSlots (β : BoundCtx (Ty Base) n) (extra : List (Option W × Ty Base)) :
    BoundCtx.Renaming β (extendedTypes β extra) :=
  ⟨Fin.castAdd extra.length, fun i => by simp [extendedTypes]⟩

/-- Every retained slot selects the renamed original name. -/
theorem extendedNames_original (extra : List (Option W × Ty Base)) (i : Fin n) :
    extendedNames plan names extra ((originalSlots β extra).toFun i) =
      (names i).map plan.register := by
  simp [extendedNames, originalSlots]

/-- The typed embedding of old slots also preserves their store projections. -/
theorem originalSlots_agree {α : Type u} (extra : List (Option W × Ty Base)) (store : V → Value α)
    (i : Fin n) :
    Certified.captureEnv (extendedNames plan names extra) (plan.renameStore store)
        ((originalSlots β extra).toFun i).val = Certified.captureEnv names store i.val := by
  simp only [Certified.captureEnv, ((originalSlots β extra).toFun i).isLt, i.isLt, dite_true]
  change (extendedNames plan names extra ((originalSlots β extra).toFun i)).elim .unit
    (plan.renameStore store) = (names i).elim .unit store
  simp [extendedNames_original, Plan.renameStore, Function.comp_def]

end Captures

section Execution

universe u v
variable {V W K J Base α : Type (u + 1)} {E : Type u → Type u} {F : Type v} {n : Nat}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] [HasTy F (Ty Base)]
  {plan : Plan V W K J} {source : Graph V K F} {inputs : List V}
  {names : Fin n → Option V} {β : BoundCtx (Ty Base) n}
  {blocks : Fin (blockCount source) → Ty Base} {exits : Fin 1 → Ty Base}
  {original : Certified.Admission source inputs names β blocks exits}

/-- A successful generation result gives equal packed executions even when
the forwarding block requires additional capture slots. The target reads the
same source store through the register equivalence. -/
theorem Generated.packed_eq (result : Generated plan source inputs names β exits)
    (leftClosed : Closed original) (instr : Primitive E F α) (store : V → Value α) :
    packedObservation leftClosed instr store =
      packedObservation result.closed instr (plan.renameStore store) := by
  rw [packedObservation_eq_sourceObservation, packedObservation_eq_sourceObservation]
  exact source_eq result.checked instr store

end Execution

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
