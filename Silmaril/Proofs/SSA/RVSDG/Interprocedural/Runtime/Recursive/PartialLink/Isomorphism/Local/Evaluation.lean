module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments

import Mathlib.Data.Fin.Embedding

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Proofs

open Continuation.Partial (Primitives Eval Site)
open Isomorphism.Proofs (LocalsRelated read_related)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {rename : Renaming}
variable {args outs head : Ports (Ty V S)} {pastL pastR sigsL sigsR : List (Ports (Ty V S))}

theorem graph_iso {argsL argsR outsL outsR : Ports (Ty V S)}
    {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
    (checked : GraphRenumbered Op rename left right) : Graph.Isomorphic Op left right := by
  induction checked with
  | intro entry exit positions _ labels inputs results _ children =>
    exact .intro entry exit positions labels inputs results children

private theorem undo_rename {n : Nat} (ids : Fin n ≃ Fin n) (vertex : Nat) :
    renameVertex ids.symm (renameVertex ids vertex) = vertex := by
  by_cases inside : vertex < n
  · simp only [renameVertex, dite_eq_left inside, dite_eq_left (ids ⟨vertex, inside⟩).isLt]
    exact congrArg Fin.val (ids.symm_apply_apply ⟨vertex, inside⟩)
  · simp only [renameVertex, dite_eq_right inside]

private def extend {n k : Nat} (ids : Fin n ≃ Fin k) : Nat ≃ Nat := by
  have same : n = k := Fin.equiv_iff_eq.mp ⟨ids⟩
  subst k
  exact ⟨renameVertex ids, renameVertex ids.symm, undo_rename ids, undo_rename ids.symm⟩

private theorem extend_at {n k : Nat} (ids : Fin n ≃ Fin k) (i : Fin n) :
    extend ids i.val = (ids i).val := by
  have same : n = k := Fin.equiv_iff_eq.mp ⟨ids⟩
  subst k
  change renameVertex ids i.val = (ids i).val
  rw [renameVertex, dite_eq_left i.isLt]

theorem from_graph_iso {argsL argsR outsL outsR : Ports (Ty V S)}
    {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
    (iso : Graph.Isomorphic Op left right) : ∃ rename, GraphRenumbered Op rename left right := by
  induction iso with
  | @intro _ _ _ _ sigsL _ left _ entry exit ids labels inputs results _ children =>
    classical
    let child (vertex arm : Nat) : Renaming :=
      if there : vertex < sigsL.length then
        if inside : arm < (left.nodes ⟨vertex, there⟩).shape.regionCount then
          Classical.choose (children ⟨vertex, there⟩ ⟨arm, inside⟩)
        else .identity
      else .identity
    refine ⟨.region (extend ids) child, .intro entry exit ids (extend_at ids) labels inputs results ?_⟩
    intro i j
    simpa only [Renaming.child, child, dite_eq_left i.isLt, dite_eq_left j.isLt] using
      Classical.choose_spec (children i j)

private theorem eval_bind {node : Node Op args pastL head} {children : Children (Term Op) node}
    {rest : Term Op args (pastL ++ [head]) sigsL outs}
    {input : Tuple m.Val args} {locals : Locals m.Val pastL}
    {store middle : σ} {value : Tuple m.Val head} {outcome : Continuation.Partial.Outcome m σ outs}
    (first : Eval primitives (nodeJob node children input locals) store (.returned value middle))
    (more : Eval primitives (.region (embed rest) input (locals.snoc value)) middle outcome) :
    Eval primitives (.region (embed (.bind node children rest)) input locals) store outcome := by
  cases node with
  | mk _ shape _ _ =>
    cases shape <;> exact .bind first more

theorem block_eval {term : Term Op args pastL sigsL outs}
    {input : Tuple m.Val args} {locals : Locals m.Val pastL} {store : σ} {location : Location}
    {outcome : Continuation.Partial.Outcome m σ outs}
    (blocked : BlockAt primitives term input locals store location outcome) :
    Eval primitives (.region (embed term) input locals) store outcome := by
  induction blocked with
  | here opcode wires input locals store undefined =>
    exact .bindBlocked (.primitiveBlocked ⟨_, _, opcode, _, _, wires.read input locals⟩ store undefined)
  | arm selection _ child =>
    apply Eval.bindBlocked
    exact selection.symm ▸ Eval.gamma child
  | later first _ more => exact eval_bind first more

private theorem empty_evaluates {entry : Ports (Ty V S)} {extra : Nat}
    (wires : Wires args pastL (.control (extra + 2) :: entry))
    (input : Tuple m.Val args) (locals : Locals m.Val pastL) (store : σ) :
    Eval primitives (nodeJob (emptyGamma (Op := Op) wires) (fun _ => .ret .nil) input locals)
      store (.returned .nil store) := by
  change Eval primitives (.node (.base (.gamma extra)) (fun _ => [])
    (fun _ => .ret .nil) (wires.read input locals)) store (.returned .nil store)
  cases wires.read input locals with
  | cons selection parameters =>
    cases selection with
    | control tag => exact .gamma (tag := tag) (Eval.ret (past := []) .nil parameters PUnit.unit store)

private theorem prepend
    {nodeL : Node Op args pastL head} {nodeR : Node Op args pastR head}
    {childrenL : Children (Term Op) nodeL} {childrenR : Children (Term Op) nodeR}
    {left : Term Op args (pastL ++ [head]) sigsL outs} {right : Term Op args (pastR ++ [head]) sigsR outs}
    {inputL inputR : Tuple m.Val args} {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    {store middle : σ} {valueL valueR : Tuple m.Val head} {outL outR : Continuation.Partial.Outcome m σ outs}
    (firstL : Eval primitives (nodeJob nodeL childrenL inputL localsL) store (.returned valueL middle))
    (firstR : Eval primitives (nodeJob nodeR childrenR inputR localsR) store (.returned valueR middle))
    (more : EvaluationPair primitives ids rename (left := left) (right := right)
      inputL inputR (localsL.snoc valueL) (localsR.snoc valueR) middle outL outR) :
    EvaluationPair primitives ids rename (left := .bind nodeL childrenL left) (right := .bind nodeR childrenR right)
      inputL inputR localsL localsR store outL outR := by
  cases more with
  | returned values ranL ranR => exact .returned values (eval_bind firstL ranL) (eval_bind firstR ranR)
  | blocked location sites ranL ranR => exact .blocked location sites (.later firstL ranL) (.later firstR ranR)

private theorem evaluate {left : Term Op args pastL sigsL outs} {right : Term Op args pastR sigsR outs}
    (schedule : Schedule Op rename left right) (respects : ActionsRespect primitives ids)
    {inputL inputR : Tuple m.Val args} {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (inputs : TupleRelated m ids inputL inputR) (locals : LocalsRelated m ids rename.vertices localsL localsR) (store : σ) :
    ∃ outL outR, EvaluationPair primitives ids rename (left := left) (right := right)
      inputL inputR localsL localsR store outL outR := by
  induction schedule generalizing store with
  | ret left right edges =>
    exact ⟨_, _, .returned (read_related inputs locals left right edges) (.ret ..) (.ret ..)⟩
  | emptyLeft wires _ ih =>
    obtain ⟨_, _, more⟩ := ih inputs locals.emptyLeft store
    have first := empty_evaluates (primitives := primitives) wires inputL localsL store
    cases more with
    | returned values ranL ranR => exact ⟨_, _, .returned values (eval_bind first ranL) ranR⟩
    | blocked location sites ranL ranR => exact ⟨_, _, .blocked location sites (.later first ranL) ranR⟩
  | emptyRight wires _ ih =>
    obtain ⟨_, _, more⟩ := ih inputs locals.emptyRight store
    have first := empty_evaluates (primitives := primitives) wires inputR localsR store
    cases more with
    | returned values ranL ranR => exact ⟨_, _, .returned values ranL (eval_bind first ranR)⟩
    | blocked location sites ranL ranR => exact ⟨_, _, .blocked location sites ranL (.later first ranR)⟩
  | @bind rename _ _ ins head pastL pastR _ _ shape wireL wireR csL csR childL childR
      restL restR position edges _ _ childIH restIH =>
    have operands := read_related inputs locals wireL wireR edges
    cases shape with
    | simple opcode =>
      let siteL : Site m := ⟨_, _, opcode, csL, fun i => embed (childL i), wireL.read inputL localsL⟩
      let siteR : Site m := ⟨_, _, opcode, csR, fun i => embed (childR i), wireR.read inputR localsR⟩
      have site : SitesRelated m ids siteL siteR := by
        have sigs : csL = csR := funext (fun i => i.elim0)
        subst csR
        have children : childL = childR := funext (fun i => i.elim0)
        subst childR
        exact .same operands
      have agreement := respects opcode operands store
      generalize foundL : (primitives.step opcode (wireL.read inputL localsL)).run store = resultL at agreement
      generalize foundR : (primitives.step opcode (wireR.read inputR localsR)).run store = resultR at agreement
      cases agreement with
      | undefined =>
        refine ⟨_, _, .blocked (pendingR := .bind (embed restR) inputR localsR .empty)
          (.here pastL.length) site (.here opcode wireL inputL localsL store foundL) ?_⟩
        rw [Renaming.location, position]
        exact .here opcode wireR inputR localsR store foundR
      | returned values middle =>
        obtain ⟨_, _, more⟩ := restIH inputs (locals.snoc rename.vertices.injective position values) middle
        exact ⟨_, _, prepend (.primitive siteL (foundL.symm ▸ _root_.Part.mem_some _))
          (.primitive siteR (foundR.symm ▸ _root_.Part.mem_some _)) more⟩
    | @gamma entry _ extra =>
      cases readL : wireL.read inputL localsL with
      | cons tagL entryL =>
        cases readR : wireR.read inputR localsR with
        | cons tagR entryR =>
          rw [readL, readR] at operands
          cases operands with
          | cons selectors parameters =>
            cases selectors with
            | control tag =>
              obtain ⟨_, _, paired⟩ := childIH tag parameters LocalsRelated.empty store
              cases paired with
              | returned values ranL ranR =>
                obtain ⟨_, _, more⟩ := restIH inputs (locals.snoc rename.vertices.injective position values) _
                refine ⟨_, _, prepend (nodeL := ⟨_, .gamma extra, wireL, csL⟩)
                  (nodeR := ⟨_, .gamma extra, wireR, csR⟩) ?_ ?_ more⟩
                · change Eval primitives (.node (.base (.gamma (entry := entry) (exit := head) extra))
                    csL (fun i => embed (childL i)) (wireL.read inputL localsL)) _ _
                  rw [readL]
                  exact .gamma ranL
                · change Eval primitives (.node (.base (.gamma (entry := entry) (exit := head) extra))
                    csR (fun i => embed (childR i)) (wireR.read inputR localsR)) _ _
                  rw [readR]
                  exact .gamma ranR
              | @blocked _ _ _ pendingR _ location sites ranL ranR =>
                refine ⟨_, _, .blocked (pendingR := .bind (embed restR) inputR localsR pendingR)
                  (.arm pastL.length tag.val location) sites (.arm readL ranL) ?_⟩
                rw [Renaming.location, position]
                exact .arm readR ranR

theorem graph_evaluate {left : Graph Op args [] sigsL outs} {right : Graph Op args [] sigsR outs}
    (code : OrderedGraph rename left right) (respects : ActionsRespect primitives ids)
    {inputL inputR : Tuple m.Val args} (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    ∃ outL outR, EvaluationPair primitives ids rename (left := left.toTerm) (right := right.toTerm)
      inputL inputR PUnit.unit PUnit.unit store outL outR :=
  evaluate code.schedule respects inputs LocalsRelated.empty store

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Proofs
