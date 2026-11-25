module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Proofs

open Continuation.Partial (Primitives Eval Site)
open Continuation.Descent (Pending)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

inductive InitializerOutcomesRelated (m : Machine.{u, v, w} Op) (ids : GlobalRel) (σ : Type (max u v w))
    (ports : Ports (Ty V S)) : Continuation.Partial.Outcome m σ ports → Continuation.Partial.Outcome m σ ports → Prop where
  | returned {left right : Tuple m.Val ports} (values : TupleRelated m ids left right) (store : σ) :
    InitializerOutcomesRelated m ids σ ports (.returned left store) (.returned right store)
  | blocked {siteL siteR : Site m} {pendingL : Pending m siteL.outs ports} {pendingR : Pending m siteR.outs ports}
      (sites : SitesRelated m ids siteL siteR) (store : σ) :
    InitializerOutcomesRelated m ids σ ports (.blocked siteL pendingL store) (.blocked siteR pendingR store)

abbrev EvaluationsRelated (primitives : Primitives m σ) (ids : GlobalRel)
    (left right : Job m outs) (store : σ) : Prop :=
  ∃ outcomeL outcomeR, Eval primitives left store outcomeL ∧ Eval primitives right store outcomeR ∧
    InitializerOutcomesRelated m ids σ outs outcomeL outcomeR

private theorem primitive_related (respects : ActionsRespect primitives ids) (site : Site m)
    {input : Tuple m.Val site.ins} (operands : TupleRelated m ids site.input input) (store : σ) :
    EvaluationsRelated primitives ids site.job ({site with input := input} : Site m).job store := by
  have agreement := respects site.opcode operands store
  generalize foundL : (primitives.step site.opcode site.input).run store = resultL at agreement
  generalize foundR : (primitives.step site.opcode input).run store = resultR at agreement
  cases agreement with
  | undefined =>
    exact ⟨_, _, .primitiveBlocked site store foundL, .primitiveBlocked {site with input := input} store foundR,
      .blocked (.same operands) store⟩
  | returned values middle =>
    exact ⟨_, _, .primitive site (foundL.symm ▸ _root_.Part.mem_some _),
      .primitive {site with input := input} (foundR.symm ▸ _root_.Part.mem_some _), .returned values middle⟩

theorem initializer_related (respects : ActionsRespect primitives ids)
    (term : Term Op args past sigs outs) {inputL inputR : Tuple m.Val args}
    {localsL localsR : Locals m.Val past} (inputs : TupleRelated m ids inputL inputR)
    (locals : LocalsRelated m ids id localsL localsR) (store : σ) :
    EvaluationsRelated primitives ids (.region (embed term) inputL localsL) (.region (embed term) inputR localsR)
      store := by
  induction term generalizing store with
  | ret wires =>
    exact ⟨_, _, .ret wires inputL localsL store, .ret wires inputR localsR store,
      .returned (read_same inputs locals wires) store⟩
  | @bind _ produced _ _ _ node children rest childIH restIH =>
    cases node with
    | mk ins shape wires cs =>
      have operands := read_same inputs locals wires
      cases shape with
      | simple opcode =>
        let site : Site m := ⟨_, _, opcode, cs, fun i => embed (children i), wires.read inputL localsL⟩
        obtain ⟨_, _, left, right, result⟩ := primitive_related respects site operands store
        cases result with
        | returned values middle =>
          obtain ⟨_, _, moreL, moreR, pair⟩ := restIH inputs (locals.snoc (fun _ _ equal => equal) rfl values) middle
          exact ⟨_, _, .bind left moreL, .bind right moreR, pair⟩
        | blocked sites stopped =>
          exact ⟨_, _, .bindBlocked left, .bindBlocked right, .blocked sites stopped⟩
      | @gamma entry _ extra =>
        let kind : NestedTheta.Kind (Instruction Op) (.control (extra + 2) :: entry) produced :=
          .base (.gamma extra)
        have evaluated : EvaluationsRelated primitives ids
            (.node kind cs (fun i => embed (children i)) (wires.read inputL localsL))
            (.node kind cs (fun i => embed (children i)) (wires.read inputR localsR)) store := by
          cases readL : wires.read inputL localsL with
          | cons tagL entryL =>
            cases readR : wires.read inputR localsR with
            | cons tagR entryR =>
              rw [readL, readR] at operands
              cases operands with
              | cons selectors parameters =>
                cases selectors with
                | control tag =>
                  obtain ⟨_, _, left, right, result⟩ := childIH tag parameters LocalsRelated.empty store
                  exact ⟨_, _, .gamma left, .gamma right, result⟩
        obtain ⟨_, _, left, right, result⟩ := evaluated
        cases result with
        | returned values middle =>
          obtain ⟨_, _, moreL, moreR, pair⟩ := restIH inputs (locals.snoc (fun _ _ equal => equal) rfl values) middle
          exact ⟨_, _, .bind left moreL, .bind right moreR, pair⟩
        | blocked sites stopped =>
          exact ⟨_, _, .bindBlocked left, .bindBlocked right, .blocked sites stopped⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Proofs
