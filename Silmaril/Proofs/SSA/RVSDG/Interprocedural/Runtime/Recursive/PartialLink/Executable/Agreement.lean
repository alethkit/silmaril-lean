module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Proofs

open Continuation.Partial (Eval Site)
open Continuation.Partial.Executable (Actions Observation observe runFor)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

theorem evalInitializer_spec (actions : Actions m σ) (term : RVSDG.Term Op args past sigs outs)
    (inputs : Tuple m.Val args) (locals : Locals m.Val past) (store : σ) :
    Eval actions.toPrimitives (.region (embed term) inputs locals) store
      (evalInitializer actions term inputs locals store) := by
  induction term generalizing store with
  | ret wires => exact .ret wires inputs locals store
  | bind node children rest childIH restIH =>
    cases node with
    | mk ins shape wires cs =>
      cases shape with
      | simple opcode =>
        let site : Site m := ⟨_, _, opcode, cs, fun i => embed (children i), wires.read inputs locals⟩
        cases ran : (actions.step opcode (wires.read inputs locals)).run store with
        | none =>
          simp only [evalInitializer, ran]
          have absent : (actions.toPrimitives.step site.opcode site.input).run store = _root_.Part.none := by
            change _root_.Part.ofOption ((actions.step opcode (wires.read inputs locals)).run store) = _
            rw [ran]
            rfl
          exact .bindBlocked (.primitiveBlocked site store absent)
        | some pair =>
          obtain ⟨values, middle⟩ := pair
          simp only [evalInitializer, ran]
          have found : (values, middle) ∈ (actions.toPrimitives.step site.opcode site.input).run store := by
            change (values, middle) ∈ _root_.Part.ofOption ((actions.step opcode (wires.read inputs locals)).run store)
            rw [ran]
            exact _root_.Part.mem_some _
          exact .bind (.primitive site found) (restIH inputs (locals.snoc values) middle)
      | gamma extra =>
        cases read : wires.read inputs locals with
        | cons tag entry =>
          cases tag with
          | control tag =>
            have evaluated := childIH tag entry PUnit.unit store
            cases ran : evalInitializer actions (children tag) entry PUnit.unit store with
            | returned values middle =>
              rw [ran] at evaluated
              simp only [evalInitializer, read, ran]
              refine .bind ?_ (restIH inputs (locals.snoc values) middle)
              exact read.symm ▸ .gamma evaluated
            | blocked site pending stopped =>
              rw [ran] at evaluated
              simp only [evalInitializer, read, ran]
              refine .bindBlocked (site := site) (pending := pending) (stopped := stopped) ?_
              exact read.symm ▸ .gamma evaluated

private theorem linkVertex_spec (actions : Actions m σ) (unitId : Nat) (inputs : Tuple m.Val args)
    (locals : Locals m.Val past) (vertex : Vertex Op args past outs) (store : σ) :
    LinksVertex actions.toPrimitives unitId inputs locals vertex store (linkVertex actions unitId inputs locals vertex store) := by
  cases vertex with
  | lambda => rfl
  | phi => rfl
  | delta delta =>
    have evaluated := evalInitializer_spec actions delta.initializer.toTerm (delta.captures.read inputs locals) PUnit.unit store
    cases ran : evalInitializer actions delta.initializer.toTerm (delta.captures.read inputs locals) PUnit.unit store with
    | returned values middle =>
      rw [ran] at evaluated
      simp only [linkVertex, LinksVertex, ran]
      exact LinksDelta.linked evaluated
    | blocked site pending stopped =>
      rw [ran] at evaluated
      simp only [linkVertex, LinksVertex, ran]
      exact LinksDelta.undefined evaluated

private theorem linkTable_spec (actions : Actions m σ) (unitId : Nat) (inputs : Tuple m.Val args)
    (locals : Locals m.Val past) (table : VertexTable Op args past sigs)
    (results : Wires args (extend past sigs) outs) (store : σ) :
    LinksTable actions.toPrimitives unitId inputs outs locals table results store
      (linkTable actions unitId inputs past sigs locals table results store) := by
  induction sigs generalizing past store with
  | nil => exact .ret locals table results store
  | cons head tail ih =>
    have evaluated := linkVertex_spec actions unitId inputs locals (table 0) store
    cases ran : linkVertex actions unitId inputs locals (table 0) store with
    | linked values middle =>
      rw [ran] at evaluated
      rw [linkTable, ran]
      exact .bind evaluated (ih (locals.snoc values) (fun i => table i.succ) results middle)
    | undefined failure =>
      rw [ran] at evaluated
      rw [linkTable, ran]
      exact .stop evaluated

theorem link_spec (actions : Actions m σ) (unitId : Nat) (graph : Omega Op args outs sigs)
    (inputs : Tuple m.Val args) (store : σ) :
    Links actions.toPrimitives unitId graph inputs store (link actions unitId graph inputs store) :=
  linkTable_spec actions unitId inputs (past := []) PUnit.unit graph.region.vertices graph.region.results store

theorem start_eq {results : Ports (Ty V S)} (request : Invocation.Request m σ results) (actions : Actions m σ) :
    start actions request.unitId request.graph request.imported request.port request.arguments request.initialStore =
      request.start actions.toPrimitives := by
  have linked := outcome_unique (link_spec actions request.unitId request.graph request.imported request.initialStore)
    (PartialLink.link_spec (primitives := actions.toPrimitives))
  rw [start, linked, Invocation.Request.start]
  cases PartialLink.link actions.toPrimitives request.unitId request.graph request.imported request.initialStore <;> rfl

theorem run_error_iff {results : Ports (Ty V S)} (request : Invocation.Request m σ results)
    (actions : Actions m σ) (fuel : Nat) {failure : Failure m σ} :
    run actions fuel request.unitId request.graph request.imported request.port request.arguments request.initialStore =
      .error failure ↔ request.Links actions.toPrimitives (.undefined failure) := by
  rw [run, start_eq request actions, ← Invocation.start_error_iff]
  cases request.start actions.toPrimitives <;> simp [Except.map]

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Proofs
