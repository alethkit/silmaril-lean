module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration

open Activation (Inputs)
open Diamond (Model Signature Ty ValueSort sortValue)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {m : Model.{u,v,w} Op}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- Successful steps account for the exact size change and consume at most the budget. -/
theorem run_progress (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    let result := run fuel loop
    result.rewrite.headerSigs.length + result.deletions = headerSigs.length ∧
      result.deletions ≤ fuel :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.run_progress fuel loop

/-- One unit of fuel per binding suffices to reach a loop on which the
native step returns `none`. This includes a failed view build. -/
theorem run_stops_of_fuel (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (enough : headerSigs.length ≤ fuel) :
    Builder.optimize? (run fuel loop).rewrite.graph = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.run_stops fuel loop enough

/-- Every iteration budget preserves the evaluator at the same backedge budget. -/
theorem run_evalBackedges (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (input : Inputs m inputs) (budget : Nat) :
    (run fuel loop).rewrite.graph.evalBackedges m budget input = loop.evalBackedges m budget input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.run_eval m input budget fuel loop

/-- Every iteration budget preserves and reflects finite returns. -/
theorem run_finite_returns (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (input : Inputs m inputs) (value : sortValue m.value out) :
    (run fuel loop).rewrite.graph.Returns m input value ↔ loop.Returns m input value :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.run_returns m input value fuel loop

/-- The default run preserves every bounded evaluation, including budget exhaustion. -/
theorem normalize_evalBackedges (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (input : Inputs m inputs) (budget : Nat) :
    (normalize loop).rewrite.graph.evalBackedges m budget input = loop.evalBackedges m budget input :=
  run_evalBackedges headerSigs.length loop input budget

/-- The default run preserves and reflects every finite return. -/
theorem normalize_returns (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (input : Inputs m inputs) (value : sortValue m.value out) :
    (normalize loop).rewrite.graph.Returns m input value ↔ loop.Returns m input value :=
  run_finite_returns headerSigs.length loop input value

/-- When a fresh certificate exists for the final loop, its freshly
enumerated proposals contain no accepted shrinking step. -/
theorem normalize_no_candidate (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    {built : Builder.Built (normalize loop).rewrite.graph}
    (admitted : Builder.build? (normalize loop).rewrite.graph = some built) :
    ∀ proposal ∈ Pass.proposals built.view,
      Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.normalize_exhausts loop admitted

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration
