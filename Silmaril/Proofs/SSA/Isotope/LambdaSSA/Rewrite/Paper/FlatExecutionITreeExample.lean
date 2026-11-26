module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Thms

/-! # A visible self-back edge in a typed packed CFG -/

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionITreeExample

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open FiniteCFG Semantics.Interaction Elgot.ITree

private inductive Op where
  | start | poll

private abbrev Choice : Ty Empty := .coprod .unit .unit

local instance : HasTy Op (Ty Empty) where
  src _ := .unit
  trg _ := Choice

private def graph : FiniteCFG Op 1 1 0 :=
  ⟨.br 0 (.op .start .unit), fun _ =>
    .case (.bv 0) (.br 0 (.op .poll (.bv 0))) (.br 1 (.bv 0))⟩

private theorem graph_typed : graph.HasType .nil (fun _ => Choice) (fun _ => .unit) :=
  ⟨.br (.op .unit), fun _ => .case .bv (.br (.op .bv)) (.br .bv)⟩

private def env : Semantics.Env Empty := fun _ => .unit

private abbrev Run := Tree (Event Op Empty) (Transfer Empty)

private noncomputable def step (p : BlockInput Empty 1) :
    Tree (Event Op Empty) (Transfer Empty ⊕ BlockInput Empty 1) :=
  region request (Semantics.extend env p.2) (graph.block p.1).erase >>= fun out =>
    pure (splitTransfer 1 out)

private noncomputable def next (reply : Value Empty) : Run :=
  iterate step (0, reply) >>= fun p => pure (packedTreeOutput p)

private theorem go_again :
    next (.inl .unit) = vis (.call .poll .unit) next := by
  have unfoldStep := congrFun (iterate_fixpoint step) (0, Value.inl Value.unit)
  change iterate step (0, .inl .unit) =
    (step (0, .inl .unit) >>= Sum.elim pure (iterate step)) at unfoldStep
  rw [next, unfoldStep]
  simp [step, graph, Flat.erase, Morphism.CaseSSA.erase, region, term, request, splitTransfer, -bind_pure_comp]
  rfl

private theorem leave :
    next (.inr .unit) = ret (0, .inl .unit) := by
  have unfoldStep := congrFun (iterate_fixpoint step) (0, Value.inr Value.unit)
  change iterate step (0, .inr .unit) =
    (step (0, .inr .unit) >>= Sum.elim pure (iterate step)) at unfoldStep
  rw [next, unfoldStep]
  simp [step, graph, Flat.erase, Morphism.CaseSSA.erase, region, term, splitTransfer,
    packedTreeOutput, Region.packedExitValue]
  rfl

-- Start is visible first. A left reply reaches the poll on the actual back
-- edge and a second left reply reaches the same poll again. A right reply
-- there leaves through the sole packed outward label.
example :
    out (region request env (packedExecutionRegion graph_typed)) =
        Part.some (.vis (.call .start .unit) next) ∧
      out (next (.inl .unit)) = Part.some (.vis (.call .poll .unit) next) ∧
      out (next (.inr .unit)) = Part.some (.ret (0, .inl .unit)) := by
  refine ⟨?_, by simp only [go_again, out_vis], by simp only [leave, out_ret]⟩
  rw [packedExecution_tree request]
  change out ((region request env graph.entry.erase >>= fun p =>
    Sum.elim pure (iterate step) (splitTransfer 1 p)) >>= fun p => pure (packedTreeOutput p)) = _
  simp [graph, Flat.erase, Morphism.CaseSSA.erase, region, term, request, splitTransfer, -bind_pure_comp]
  rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionITreeExample
