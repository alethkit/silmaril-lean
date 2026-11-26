module

public import Silmaril.Semantics.ITree.Trace.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.PackedTrace

/-! # Finite trace refinement for packed CFG executions -/

public section

universe u v w x

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open Semantics (Env extend)
open Semantics.Interaction (Primitive Transfer BlockInput region splitTransfer)
open Silmaril.Elgot.ITree (Tree TraceLE)

variable {Events : Type w → Type w} {Φ : Type v} {α : Type u}
  {τ : Type x} [TypeFormers τ] [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {L : Fin exits → τ}
  {g h : FiniteCFG Φ blocks exits 0}

/-- For graphs on a common positional interface, refinement at the entry and
at each block with the same incoming packet implies refinement of their
actual packed executions. The two primitive evaluators and environments may
differ. -/
theorem packedExecution_traceLE (ins ins' : Primitive Events Φ α) (env env' : Env α)
    (hg : HasType .nil R L g) (hh : HasType .nil R L h)
    (entry : TraceLE.{w, u} (region ins env g.entry.erase) (region ins' env' h.entry.erase))
    (block : ∀ i (packet : Value α),
      TraceLE.{w, u} (region ins (extend env packet) (g.block i).erase)
        (region ins' (extend env' packet) (h.block i).erase)) :
    TraceLE.{w, u} (region ins env (packedExecutionRegion hg))
      (region ins' env' (packedExecutionRegion hh)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.FiniteCFG.packedExecution_traceLE ins ins' env env' hg hh
    entry block

end Silmaril.Isotope.LambdaSSA.FiniteCFG
