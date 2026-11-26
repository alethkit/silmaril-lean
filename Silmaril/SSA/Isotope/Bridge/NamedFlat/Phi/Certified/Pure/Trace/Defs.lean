module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.ITree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Defs

/-! # Comparing certified φ graphs at a matched interface -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture

open Silmaril.SSA.LambdaRTL
open Silmaril.Elgot.ITree (Tree)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction (Primitive Transfer region)

universe u v w
variable {Base : Type u} {n : Nat}

/-- The positional input profile and the sole external result type agree.
Internal block profiles and register names are independent. -/
structure InterfaceMatch (left right : BoundCtx (Ty Base) n)
    (leftExit rightExit : Fin 1 → Ty Base) : Prop where
  slots : left = right
  exit : leftExit 0 = rightExit 0

/-- A common input observation with typed interface alignment and equal
version-zero values at every selected capture position. -/
structure MatchedInputs {V W α : Type u} (left right : BoundCtx (Ty Base) n)
    (leftExit rightExit : Fin 1 → Ty Base)
    (leftNames : Fin n → Option V) (rightNames : Fin n → Option W) where
  interface : InterfaceMatch left right leftExit rightExit
  leftStore : V → Value α
  rightStore : W → Value α
  slots : ∀ i : Fin n, captureEnv leftNames leftStore i.val = captureEnv rightNames rightStore i.val

variable {Events : Type w → Type w} {F : Type v} {V K α : Type (w + 1)}
  [DecidableEq V] [DecidableEq K]

/-- Observe the independent φ evaluator in the common outward coordinates.
Requests and replies pass through unchanged. Only returns are numbered and tagged. -/
noncomputable def sourceObservation (instr : Primitive Events F α)
    (source : CFG.Cyclic.Phi.Graph V K F) (store : V → Value α) : Tree Events (Transfer α) :=
  runTree instr source store >>= fun p => pure (FiniteCFG.packedTreeOutput (treeExitNumber [none] p))

/-- Observe the actual checked packed dispatcher with pure projections from
the specified source store. -/
noncomputable def packedObservation {Base : Type (w + 1)} [HasTy F (Ty Base)]
    {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
    {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
    {admitted : Admission source inputs captures β R L}
    (closed : Closed admitted) (instr : Primitive Events F α) (store : V → Value α) :
    Tree Events (Transfer α) :=
  region (treePrimitives (β := β) instr (captureEnv captures store))
    (fun _ => .unit) (FiniteCFG.packedExecutionRegion closed.typed)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
