module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Defs

/-! # Local simulation witnesses for a checked φ backedge split -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction (Primitive)

universe u v
variable {V W K J Base α : Type (u + 1)} {F : Type v} {E : Type u → Type u} {n : Nat}
variable (plan : Plan V W K J)

/-- Align the typed outward profiles and names selected at version zero.
The two internal block profiles are checked independently by admission. -/
structure InputAlignment (left right : BoundCtx (Ty Base) n)
    (leftExit rightExit : Fin 1 → Ty Base)
    (leftNames : Fin n → Option V) (rightNames : Fin n → Option W) : Prop where
  interface : InterfaceMatch left right leftExit rightExit
  captures : ∀ i, rightNames i = (leftNames i).map plan.register

variable [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]

/-- Both local simulations, including the entry fact for every renamed input.
No runtime relation or primitive law is supplied by callers. -/
structure Witness (instr : Primitive E F α) (source : Graph V K F) (target : Graph W J F) where
  forward : Simulation instr instr source target
  backward : Simulation instr instr target source
  enterForward (store : V → Value α) :
    forward.residual (entryTree instr source store) (entryTree instr target (plan.renameStore store))
  enterBackward (store : V → Value α) :
    backward.residual (entryTree instr target (plan.renameStore store)) (entryTree instr source store)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
