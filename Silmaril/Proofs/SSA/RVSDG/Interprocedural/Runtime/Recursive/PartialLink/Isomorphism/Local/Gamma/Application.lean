module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Feedback
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Regions
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial
open Continuation.Descent (Pending)
open Isomorphism.Proofs (LocalsRelated read_same)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {args outs captured : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {fn : Function V S}

private theorem application_reaches {entry : Tuple m.Val args} {inputs : Wires args [] (fn.port :: fn.args)}
    {callee : m.Val fn.port} {arguments : Tuple m.Val fn.args} {store : σ}
    {target : Feedback.Restart m σ} {pending : Pending m target.carried fn.results}
    (selected : inputs.read entry PUnit.unit = .cons callee arguments)
    (ran : Feedback.Reaches primitives (.call callee arguments) store target pending) :
    Feedback.Reaches primitives (.node (applicationVertex fn inputs).kind (applicationVertex fn inputs).childSigs
      (fun i => i.elim0) (inputs.read entry PUnit.unit)) store target pending :=
  selected.symm ▸ Feedback.Reaches.apply (fn := fn) (cs := fun _ => []) (children := fun i => i.elim0) ran

private theorem application_then
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    {tailL tailR : List (Ports (Ty V S))}
    {suffixL : Term Op args [fn.results] tailL outs} {suffixR : Term Op args [fn.results] tailR outs}
    (respects : ActionsRespect primitives ids) (inputs : Wires args [] (fn.port :: fn.args))
    (suffix : Local.Schedule Op .identity suffixL suffixR)
    {entryL entryR : Tuple m.Val args} (entries : TupleRelated m ids entryL entryR)
    {captL captR : Tuple m.Val captured} {argsL argsR : Tuple m.Val fn.args} {store : σ}
    (selectL : inputs.read entryL PUnit.unit = .cons (.closure captL left.toGraph) argsL)
    (selectR : inputs.read entryR PUnit.unit = .cons (.closure captR right.toGraph) argsR)
    (observed : RegionPair primitives ids mapping left right
      (prependContext argsL captL) (prependContext argsR captR) store) :
    RegionPair primitives ids mapping (applicationThen fn inputs suffixL) (applicationThen fn inputs suffixR)
      entryL entryR store := by
  have actualL := open_lambda left captL argsL
  have actualR := open_lambda right captR argsR
  cases observed with
  | @returned _ _ middle values ranL ranR =>
    have calledL := Eval.call (actualL.symm ▸ ranL)
    have calledR := Eval.call (actualR.symm ▸ ranR)
    obtain ⟨_, _, resumed⟩ := Local.suffix_evaluate suffix respects entries values middle
    cases resumed with
    | returned results restL restR =>
      exact .returned results (.bind (node := applicationVertex fn inputs) (application_eval selectL calledL) restL)
        (.bind (node := applicationVertex fn inputs) (application_eval selectR calledR) restR)
    | blocked location sites restL restR =>
      exact .blocked (.afterApplication inputs suffixL suffixR selectL selectR calledL calledR location sites restL restR)
  | blocked stopped =>
    exact .blocked (.applicationThen inputs suffixL suffixR selectL selectR stopped)
  | productive run =>
    refine .productive (productive_map run ?_ ?_)
    · intro target pending reached
      exact ⟨.bind (past := []) (embed suffixL) entryL PUnit.unit pending,
        .inside (node := applicationVertex fn inputs)
          (application_reaches selectL (.call (actualL.symm ▸ reached)))⟩
    · intro target pending reached
      exact ⟨.bind (past := []) (embed suffixR) entryR PUnit.unit pending,
        .inside (node := applicationVertex fn inputs)
          (application_reaches selectR (.call (actualR.symm ▸ reached)))⟩

private theorem fixed_wires {ports : Ports (Ty V S)} (wires : Wires args [fn.results] ports) :
    wires.addresses.map (Address.rename Renaming.identity.vertices) = wires.addresses := by
  induction wires with
  | nil => rfl
  | cons origin _ ih =>
    cases origin <;> simp [Wires.addresses, Origin.address, Address.rename, Renaming.vertices,
      show List.map (Address.rename id) (Wires.addresses _) = _ from ih]

theorem application
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    (code : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (inputs : Wires args [] (fn.port :: fn.args)) (outputs : Wires args [fn.results] outs)
    {entryL entryR : Tuple m.Val args} (entries : TupleRelated m ids entryL entryR)
    {captL captR : Tuple m.Val captured} (captures : TupleRelated m ids captL captR)
    {argsL argsR : Tuple m.Val fn.args} (arguments : TupleRelated m ids argsL argsR)
    (selectL : inputs.read entryL PUnit.unit = .cons (.closure captL left.toGraph) argsL)
    (selectR : inputs.read entryR PUnit.unit = .cons (.closure captR right.toGraph) argsR) (store : σ) :
    RegionPair primitives ids mapping (applicationCode fn inputs outputs) (applicationCode fn inputs outputs)
      entryL entryR store :=
  application_then respects inputs (.ret outputs outputs (fixed_wires outputs)) entries selectL selectR
    (regions code respects (prepend_related captures arguments) store)

/-- A static caller reads its function from its first captured port. -/
theorem captured_application
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    (code : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (arguments : Wires (fn.port :: args) [] fn.args) (outputs : Wires (fn.port :: args) [fn.results] outs)
    {tailL tailR : Tuple m.Val args} (tails : TupleRelated m ids tailL tailR)
    {captL captR : Tuple m.Val captured} (captures : TupleRelated m ids captL captR)
    (iso : NestedTheta.Graph.Isomorphic (Instruction Op) left.toGraph right.toGraph) (store : σ) :
    RegionPair primitives ids mapping (applicationCode fn (.cons (.arg .head) arguments) outputs)
      (applicationCode fn (.cons (.arg .head) arguments) outputs)
      (.cons (.closure captL left.toGraph) tailL) (.cons (.closure captR right.toGraph) tailR) store := by
  have entries := TupleRelated.cons (ValueRelated.closure captures iso) tails
  exact application code respects (.cons (.arg .head) arguments) outputs entries captures
    (read_same entries LocalsRelated.empty arguments) rfl rfl store

theorem call_plan_regions {rank : Nat} {context params : Ports (Ty V S)}
    {capturesL capturesR : Tuple m.Val context}
    {left : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsL outs}
    {right : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsR outs}
    (plan : CallPlan m ids mapping rank capturesL capturesR left right)
    (respects : ActionsRespect primitives ids) :
    TupleRelated m ids capturesL capturesR ∧
      ∀ {argsL argsR : Tuple m.Val params}, TupleRelated m ids argsL argsR → ∀ store,
        RegionPair primitives ids mapping left right (prependContext argsL capturesL) (prependContext argsR capturesR) store := by
  induction plan with
  | body captures code =>
    exact ⟨captures, fun arguments store => regions code respects (prepend_related captures arguments) store⟩
  | application _ iso captures arguments suffix ih =>
    have paired := TupleRelated.cons (ValueRelated.closure ih.1 iso) captures
    refine ⟨paired, ?_⟩
    intro argsL argsR supplied store
    have entries := prepend_related paired supplied
    have operands := read_same entries LocalsRelated.empty arguments
    exact application_then respects (.cons (.arg .head) arguments) suffix entries rfl rfl (ih.2 operands store)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs
