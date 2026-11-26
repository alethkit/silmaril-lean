module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration
open Activation (Inputs)
open Diamond (Model Signature Ty ValueSort sortValue)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

private theorem run_none {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
    (fuel : Nat) (found : Builder.optimize? loop = none) :
    run (fuel + 1) loop = ⟨⟨headerSigs, loop⟩, 0⟩ := by
  simp only [run, found]

private theorem run_some {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
    (fuel : Nat) {next : Deletion.DeletedLoop Op inputs carried entrySigs out}
    (found : Builder.optimize? loop = some next) :
    run (fuel + 1) loop =
      ⟨(run fuel next.graph).rewrite, (run fuel next.graph).deletions + 1⟩ := by
  simp only [run, found]

theorem run_progress (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    let result := run fuel loop
    result.rewrite.headerSigs.length + result.deletions = headerSigs.length ∧
      result.deletions ≤ fuel := by
  induction fuel generalizing headerSigs with
  | zero => exact ⟨rfl, Nat.le_refl _⟩
  | succ fuel ih =>
    cases next : Builder.optimize? loop with
    | none => simp [run, next]
    | some shortened =>
      have count := Builder.optimize_count next
      have ⟨exactCount, budget⟩ := ih shortened.graph
      simp only [run, next]
      exact ⟨by omega, by omega⟩

theorem run_stops (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (enough : headerSigs.length ≤ fuel) :
    Builder.optimize? (run fuel loop).rewrite.graph = none := by
  induction fuel generalizing headerSigs with
  | zero =>
    change Builder.optimize? loop = none
    cases next : Builder.optimize? loop with
    | none => rfl
    | some shortened =>
      have count := Builder.optimize_count next
      omega
  | succ fuel ih =>
    cases next : Builder.optimize? loop with
    | none =>
      rw [run_none fuel next]
      exact next
    | some shortened =>
      have count := Builder.optimize_count next
      rw [run_some fuel next]
      exact ih shortened.graph (by omega)

theorem run_eval (m : Model.{u,v,w} Op) (input : Inputs m inputs) (budget fuel : Nat)
    (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    (run fuel loop).rewrite.graph.evalBackedges m budget input = loop.evalBackedges m budget input := by
  induction fuel generalizing headerSigs with
  | zero => rfl
  | succ fuel ih =>
    cases next : Builder.optimize? loop with
    | none => rw [run_none fuel next]
    | some shortened =>
      rw [run_some fuel next]
      exact (ih shortened.graph).trans (Builder.optimize_evalBackedges next input budget)

theorem run_returns (m : Model.{u,v,w} Op) (input : Inputs m inputs) (value : sortValue m.value out)
    (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    (run fuel loop).rewrite.graph.Returns m input value ↔ loop.Returns m input value := by
  induction fuel generalizing headerSigs with
  | zero => rfl
  | succ fuel ih =>
    cases next : Builder.optimize? loop with
    | none => rw [run_none fuel next]
    | some shortened =>
      rw [run_some fuel next]
      exact (ih shortened.graph).trans (Builder.optimize_returns next input value)

theorem normalize_exhausts (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    {built : Builder.Built (normalize loop).rewrite.graph}
    (admitted : Builder.build? (normalize loop).rewrite.graph = some built) :
    ∀ proposal ∈ Pass.proposals built.view,
      Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal = none := by
  have stopped := run_stops headerSigs.length loop (Nat.le_refl _)
  change Builder.optimize? (normalize loop).rewrite.graph = none at stopped
  rw [Builder.optimize?, admitted, Option.bind_some] at stopped
  exact (Pass.step?_eq_none_iff built.view).mp stopped

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration
