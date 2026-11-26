module

public import Silmaril.Semantics.ITree.Trace.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Thms

public section

universe u v w x

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.FiniteCFG

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.FiniteCFG

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
      (region ins' env' (packedExecutionRegion hh)) := by
  rw [packedExecution_tree, packedExecution_tree]
  refine TraceLE.bind_pure ?_ packedTreeOutput
  let leftStep (p : BlockInput α blocks) : Tree Events (Transfer α ⊕ BlockInput α blocks) :=
    region ins (extend env p.2) (g.block p.1).erase >>= fun out => pure (splitTransfer blocks out)
  let rightStep (p : BlockInput α blocks) : Tree Events (Transfer α ⊕ BlockInput α blocks) :=
    region ins' (extend env' p.2) (h.block p.1).erase >>= fun out => pure (splitTransfer blocks out)
  change TraceLE (region ins env g.entry.erase >>= fun p =>
      Sum.elim pure (Silmaril.Elgot.iter leftStep) (splitTransfer blocks p))
    (region ins' env' h.entry.erase >>= fun p =>
      Sum.elim pure (Silmaril.Elgot.iter rightStep) (splitTransfer blocks p))
  refine entry.bind fun out => ?_
  cases splitTransfer blocks out with
  | inl _ => exact TraceLE.refl _
  | inr next =>
    exact TraceLE.iter (fun p => (block p.1 p.2).bind_pure (splitTransfer blocks)) next

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.FiniteCFG
