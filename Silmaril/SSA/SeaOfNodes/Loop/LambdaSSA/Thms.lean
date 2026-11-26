module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.SSA.PhiView.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Correctness

/-! # Exact finite λSSA observations of the counted-swap profile -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

universe u v

theorem lower_hasType : lower.HasType inputContext [returnType] :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.lower_hasType

theorem incoming_distinct : edge .entry ≠ edge .backedge := fun same => by cases same

/-- Both incoming occurrences recover their original branch argument. -/
theorem edge_branch (arrival : Incoming) :
    phiView.table.branch (edge arrival) = .br 0 (edge arrival).argument := by
  rw [PhiView.branch_eq phiView]
  cases arrival <;> rfl

theorem blockArgs_roundtrip : PhiView.toBlockArgs phiView = blockArgs :=
  PhiView.toBlockArgs_ofBlockArgs blockArgs

theorem phiView_roundtrip : PhiView.ofBlockArgs (PhiView.toBlockArgs phiView) = phiView :=
  PhiView.ofBlockArgs_toBlockArgs phiView

variable (m : Diamond.Model.{0,0,u} Op) {σ : Type v}

/-- Each selected incoming branch latches its entire column from the old
environment and transfers to the header with ambient state unchanged. -/
theorem edge_transfer_iff (arrival : Incoming) (old : Env (Word m)) (start finish : σ)
    (label : Nat) (payload : Value (Word m)) :
    Semantics.Region.Eval (instruction m) old (.br (edge arrival).target (edge arrival).argument)
        start label payload finish ↔
      label = 0 ∧ payload = latchPayload m arrival old ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.edge_transfer_iff m arrival old start finish label payload

variable (args : Inputs (Word m))

/-- The actual preheader supplies the source entry latch tuple. -/
theorem entry_eval (start : σ) :
    Semantics.Region.Eval (instruction m) (inputEnv m args) entry start 0
      (packCarried m (graph.initial m (input m args))) start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.entry_eval m args start

/-- One actual header activation performs the source step. A return carries
a singleton tuple at raw label one. Feedback carries a complete tuple at zero. -/
theorem header_eval (old : Carried m) (start : σ) :
    Semantics.Region.Eval (instruction m) (extend (inputEnv m args) (packCarried m old))
        header start (stepLabel m (graph.step m (input m args) old))
          (stepPayload m (graph.step m (input m args) old)) start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.header_eval m args old start

/-- A finite target CFG suffix corresponds to a source derivation from the
same carried tuple, including the case of zero completed backedges. -/
theorem follow_iff (old : Carried m) (start finish : σ) (label : Nat) (payload : Value (Word m)) :
    Semantics.Region.Follow (instruction m) (inputEnv m args) blocks
        0 (packCarried m old) start label payload finish ↔
      ∃ count result, graph.ReturnsAfter m (input m args) count old result ∧
        label = 0 ∧ payload = packResult m result ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.follow_iff m args old start finish label payload

/-- Exact label, payload and state of every finite evaluation of the CFG. -/
theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Word m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m args) lower start label payload finish ↔
      ∃ result, graph.Returns m (input m args) result ∧
        label = 0 ∧ payload = packResult m result ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.lower_eval_iff m args start finish label payload

theorem returns_iff (start : σ) (result : Word m) :
    graph.Returns m (input m args) result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m args) lower start 0 (packResult m result) start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.returns_iff m args start result

theorem mem_denote_iff (start : σ) (result : Word m) :
    result ∈ graph.denote m (input m args) ↔
      Semantics.Region.Eval (instruction m) (inputEnv m args) lower start 0 (packResult m result) start :=
  (graph.returns_iff_mem_denote m (input m args) result).symm.trans (returns_iff m args start result)

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
