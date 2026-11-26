module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Proofs

open Continuation.Partial.Executable (Actions)
open NestedTheta.Liveness (Demand)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports : Ports (Ty V S)} {inputsL inputsR : Tuple m.Val imports}
variable {scope : Scope m} {summary : MemberSummary V S} {sigs : List (Ports (Ty V S))}
variable {actions : Actions m σ} {left right : Outcome m σ [summary.fn.port]}

private theorem binding_problem {fn : Function V S} (binding : Binding Op scope.table imports scope.past fn)
    (demand : Demand) (origin : Address) :
    origin ∈ (binding.body.liveness demand).mayOut 0 ↔ origin ∈ binding.summary.live demand := by
  rw [← binding.body.mem_liveIn_iff]
  exact List.mem_eraseDups

theorem plan_problem {tail : ModuleTerm Op imports scope.past sigs [summary.fn.port]}
    (plan : Plan inputsL inputsR scope summary tail) (demand : Demand) (origin : Address) :
    origin ∈ (plan.problem demand).mayOut 0 ↔ origin ∈ summary.live demand := by
  induction plan with
  | finish binding _ _ => exact binding_problem binding demand origin
  | finishDirect binding => exact binding_problem binding demand origin
  | lambda _ _ _ _ ih => exact ih
  | lambdaDirect _ _ ih => exact ih
  | skipLambda _ _ ih => exact ih

theorem port_agreement (analysis : ExportAnalysis actions summary left right) (demand : Demand)
    (argsL argsR : Tuple m.Val summary.fn.args)
    (captures : ∀ {ty} (p : Port summary.captures ty), analysis.liveCapture demand p = true →
      analysis.linked.capsL.get p = analysis.linked.capsR.get p)
    (formals : ∀ {ty} (p : Port summary.fn.args ty), analysis.liveFormal demand p = true →
      argsL.get p = argsR.get p) :
    InputsAgree (m := m) summary demand (prependContext argsL analysis.linked.capsL)
      (prependContext argsR analysis.linked.capsR) :=
  StaticDemand.Proofs.prepend_agrees (fun i => Address.arg i ∈ summary.live demand)
    analysis.linked.capsL analysis.linked.capsR argsL argsR
    (fun p live => captures p (List.contains_iff_mem.2 (List.mem_eraseDups.2 live)))
    (fun p live => formals p (List.contains_iff_mem.2 (List.mem_eraseDups.2 live)))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Proofs
