module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Part
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Tree

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture

open Silmaril.Isotope Silmaril.Isotope.Bridge Silmaril.SSA.LambdaRTL
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Phi (runTree)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified (Admission blockCount captureEnv)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Diverges Env)
open LambdaSSA.Semantics.Interaction (Primitive region term)
open Silmaril.Elgot.ITree (Tree)

universe u v w
variable {n : Nat}

section Admission

variable {V K Base : Type u} {F : Type v} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
  {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
  {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}

private theorem lowering (admitted : Admission source inputs captures β R L) :
    CFG.Cyclic.Phi.compile source = some (CFG.Cyclic.Versioning.compile (CFG.Cyclic.Phi.lower source)) :=
  (CFG.Cyclic.Phi.compile_eq_some_iff _ _).mpr ⟨admitted.wellFormed.normalized, rfl⟩

end Admission

private theorem capture_at {V α : Type u} (names : Fin n → Option V) (store : V → Value α) (i : Fin n) :
    captureEnv names store i.val = CFG.Cyclic.Phi.liftStore .unit store (names i) := by
  simp [captureEnv, i.isLt, CFG.Cyclic.Phi.liftStore]

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
  (NamedFlat.Phi.run_iff (lowering admitted) admitted.elaborated (capture_at captures store)).trans
    ((embed_eval prim (captureEnv captures store) admitted.graph).symm.trans
      (Capture.packed_eval_at closed.typed closed.closes
        (packetInput_eval prim (captureEnv captures store) (fun _ => .unit))).symm)

theorem packed_infinite_run_iff {V K Base F α : Type u} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
    {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
    {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
    {admitted : Admission source inputs captures β R L}
    (closed : Closed admitted) (prim : F → Value α → Part (Value α)) (store : V → Value α) :
    CFG.Cyclic.Phi.InfiniteRun (model prim) source store ↔
      Diverges (instr (partPrimitives (β := β) prim (captureEnv captures store)))
        (.region (fun _ => .unit) (FiniteCFG.packedExecutionRegion closed.typed) ()) :=
  (NamedFlat.Phi.infinite_run_iff (lowering admitted) admitted.elaborated (capture_at captures store)).trans
    ((embed_diverges prim (captureEnv captures store) admitted.graph (captureEnv captures store)).symm.trans
      ((FiniteCFG.packedExecution_diverges_iff closed.typed).trans
        (Capture.diverges_iff closed.closes (packetInput_eval prim (captureEnv captures store) (fun _ => .unit)))).symm)

theorem packed_run_tree {Events : Type w → Type w} {F : Type v}
    {V K Base α : Type (w + 1)} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
    {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
    {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
    {admitted : Admission source inputs captures β R L}
    (closed : Closed admitted) (instr : Primitive Events F α) (store : V → Value α) :
    region (treePrimitives (β := β) instr (captureEnv captures store))
        (fun _ => .unit) (FiniteCFG.packedExecutionRegion closed.typed) =
      (runTree instr source store >>= fun p => pure (FiniteCFG.packedTreeOutput (treeExitNumber [none] p))) := by
  let slots := captureEnv captures store
  let extended := treePrimitives (β := β) instr slots
  let ambient : Env α := fun _ => .unit
  have packet : term extended ambient (Morphism.CaseSSA.erase (packetInput F β)) =
      ((pure store : Tree Events (V → Value α)) >>= fun reply =>
        pure (Capture.packEnv n (captureEnv captures reply))) := by
    rw [pure_bind]
    exact packetInput_tree instr slots ambient
  have closedTree := Capture.graph_tree extended closed.closes packet
  rw [pure_bind] at closedTree
  change region extended ambient (FiniteCFG.packedExecutionRegion closed.typed) = _
  rw [FiniteCFG.packedExecution_tree extended closed.typed ambient, closedTree,
    embed_tree instr slots admitted.graph slots,
    ← NamedFlat.Phi.run_tree (lowering admitted) instr store (fun i => (captures i, 0))
      admitted.elaborated slots (capture_at captures store), bind_assoc]
  simp only [pure_bind]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
