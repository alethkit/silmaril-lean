module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Execution
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Typing

/-! # Certified φ execution with a synthesized pure capture -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Diverges)
open LambdaSSA.Semantics.Interaction (Primitive region)

universe u v w
variable {n : Nat}

section Close

variable {V K Base : Type u} {F : Type v}
  [DecidableEq V] [DecidableEq K] [DecidableEq Base] [HasTy F (Ty Base)]
  {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
  {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}

/-- Close the actual admitted table with a synthesized, typed packet expression. -/
def close (admitted : Admission source inputs captures β R L) : Option (Closed admitted) :=
  (Capture.close β R L (embed admitted.graph)
    (by exact Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.embed_typed admitted.typed)
    (packetInput F β) (by exact Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.packetInput_typed)).map
    (fun result => ⟨result.val, result.property.1, result.property.2⟩)

end Close

/-- Finite returns agree with the packed dispatcher under the canonical
pure capture. Original primitives share the caller's partial interpretation. -/
theorem packed_run_iff {V K Base F α : Type u} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
    {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
    {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
    {admitted : Admission source inputs captures β R L}
    (closed : Closed admitted) (prim : F → Value α → Part (Value α)) (store : V → Value α)
    {value : Value α} :
    (none, value) ∈ CFG.Cyclic.Phi.run (model prim) source store ↔
      LambdaSSA.Semantics.Region.Eval (instr (partPrimitives (β := β) prim (captureEnv captures store)))
        (fun _ => .unit) (FiniteCFG.packedExecutionRegion closed.typed)
        () 0 (Region.packedExitValue 0 value) () :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.packed_run_iff closed prim store

/-- The pure packet leaves the atomic infinite-path correspondence intact. -/
theorem packed_infinite_run_iff {V K Base F α : Type u} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
    {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
    {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
    {admitted : Admission source inputs captures β R L}
    (closed : Closed admitted) (prim : F → Value α → Part (Value α)) (store : V → Value α) :
    CFG.Cyclic.Phi.InfiniteRun (model prim) source store ↔
      Diverges (instr (partPrimitives (β := β) prim (captureEnv captures store)))
        (.region (fun _ => .unit) (FiniteCFG.packedExecutionRegion closed.typed) ()) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.packed_infinite_run_iff closed prim store

/-- Pure input projection introduces no visible requests. The packed tree
has the source's visible continuation and its numbered, tagged return. -/
theorem packed_run_tree {Events : Type w → Type w} {F : Type v}
    {V K Base α : Type (w + 1)} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
    {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
    {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
    {admitted : Admission source inputs captures β R L}
    (closed : Closed admitted) (instr : Primitive Events F α) (store : V → Value α) :
    region (treePrimitives (β := β) instr (captureEnv captures store))
        (fun _ => .unit) (FiniteCFG.packedExecutionRegion closed.typed) =
      (runTree instr source store >>= fun p => pure (FiniteCFG.packedTreeOutput (treeExitNumber [none] p))) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.packed_run_tree closed instr store

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
