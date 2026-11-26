module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.ITree.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Infinite.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified

/-! # End-to-end execution of a checked φ admission and typed closure -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified

open Silmaril.SSA.LambdaRTL
open Silmaril.Elgot.ITree (Tree)
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Diverges Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open LetCase.LocallyNameless (Tm)

universe u v w
variable {n : Nat}

section Atomic

variable {V K Base F α : Type u} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
  {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
  {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
  {admitted : Admission source inputs captures β R L} {packetInput : Tm Empty F 0}

/-- A finite source return agrees with the checked packed target. The capture
expression must return exactly the source store's capture record. Both sides
use the same stateless partial primitives. -/
theorem packed_run_iff (closed : Closed admitted packetInput) (prim : F → Value α → Part (Value α))
    (store : V → Value α) (ambient : Env α) {value : Value α}
    (packet : ∀ v state, LambdaSSA.Semantics.Tm.Eval (instr prim) ambient
      (Morphism.CaseSSA.erase packetInput) () v state ↔
        v = Capture.packEnv n (captureEnv captures store) ∧ state = ()) :
    (none, value) ∈ CFG.Cyclic.Phi.run (model prim) source store ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) ambient (FiniteCFG.packedExecutionRegion closed.typed)
        () 0 (Region.packedExitValue 0 value) () :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.packed_run_iff closed prim store ambient packet

/-- The checked atomic packed dispatcher diverges exactly when the source
has an infinite path of successful internal transfers. -/
theorem packed_infinite_run_iff (closed : Closed admitted packetInput)
    (prim : F → Value α → Part (Value α)) (store : V → Value α) (ambient : Env α)
    (packet : ∀ v state, LambdaSSA.Semantics.Tm.Eval (instr prim) ambient
      (Morphism.CaseSSA.erase packetInput) () v state ↔
        v = Capture.packEnv n (captureEnv captures store) ∧ state = ()) :
    CFG.Cyclic.Phi.InfiniteRun (model prim) source store ↔
      Diverges (instr prim) (.region ambient (FiniteCFG.packedExecutionRegion closed.typed) ()) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.packed_infinite_run_iff closed prim store ambient packet

end Atomic

/-- The checked packed target runs the capture producer, then the original φ
evaluator with the store for each reply. The result carries the lowering,
elaboration, typing and closure evidence, while the packet equation describes
the producer's effects and values. Both sides use the same primitive trees. -/
theorem packed_run_tree {Events : Type w → Type w} {F : Type v}
    {V K Base α Reply : Type (w + 1)} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
    {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
    {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
    {admitted : Admission source inputs captures β R L} {packetInput : Tm Empty F 0}
    (closed : Closed admitted packetInput) (instr : Primitive Events F α)
    (produce : Tree Events Reply) (store : Reply → V → Value α) (ambient : Env α)
    (packet : LambdaSSA.Semantics.Interaction.term instr ambient (Morphism.CaseSSA.erase packetInput) =
      (produce >>= fun reply => pure (Capture.packEnv n (captureEnv captures (store reply))))) :
    region instr ambient (FiniteCFG.packedExecutionRegion closed.typed) =
      (produce >>= fun reply => runTree instr source (store reply) >>= fun p =>
        pure (FiniteCFG.packedTreeOutput (treeExitNumber [none] p))) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.packed_run_tree closed instr produce store ambient packet

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified
