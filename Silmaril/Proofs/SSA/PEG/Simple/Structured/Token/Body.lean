module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Defs
public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Views

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open Simple.Proofs (NodeValues eval_append eval_lift realizes_lift get_map get_select)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {vars outs params before : List (Ty Data)} {t : Ty Data}
variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)

mutual

theorem exprExact {t : Ty Data} (rhs : Expr P vars t) {before : List (Ty Data)}
    (ctx : Tuple (Port before) vars)
    (values : NodeValues (model m) before) (store : Tuple m.Value vars)
    (entry : Realizes (model m) values ctx store) :
    let b := (expr rhs).lower (params := params) ctx
    (b.code.eval (model m) env values).get (b.refs.get .head) = rhs.eval m store := by
  cases rhs with
  | var p => exact entry _ p
  | op op args =>
    let b := (arguments args).lower (params := params) ctx
    change (collect _ (fun slot => (b.code.eval (model m) env values).get
      (b.refs.get (portAt _ slot)))).elim none (m.run op) = (args.eval m store).elim none (m.run op)
    rw [argsExact args ctx values store entry]

theorem argsExact {outs : List (Ty Data)} (args : Args P vars outs) {before : List (Ty Data)}
    (ctx : Tuple (Port before) vars)
    (values : NodeValues (model m) before) (store : Tuple m.Value vars)
    (entry : Realizes (model m) values ctx store) :
    let b := (arguments args).lower (params := params) ctx
    collect outs (fun slot => (b.code.eval (model m) env values).get
      (b.refs.get (portAt outs slot))) = args.eval m store := by
  cases args with
  | nil => rfl
  | @cons t ts rhs rest =>
    let head := (expr rhs).lower (params := params) ctx
    let tail := (arguments rest).lower (params := params) (head.code.liftRefs ctx)
    let vs := head.code.eval (model m) env values
    let vs' := tail.code.eval (model m) env vs
    change collect (t :: ts) (fun slot =>
      ((head.code.append tail.code).eval (model m) env values).get
        ((Tuple.cons (tail.code.lift (head.refs.get .head)) tail.refs).get (portAt _ slot))) = _
    rw [eval_append]
    simp only [collect, portAt, Fin.cases_zero, Fin.cases_succ, Tuple.get]
    rw [show vs'.get (tail.code.lift (head.refs.get .head)) = rhs.eval m store from
      (eval_lift _ _ _ _ _).trans (exprExact rhs ctx values store entry)]
    rw [show collect ts (fun slot => vs'.get (tail.refs.get (portAt ts slot))) =
        rest.eval m store from
      argsExact rest (head.code.liftRefs ctx) vs store
        (realizes_lift (model m) env head.code entry)]
    simp only [Args.eval, Expr.eval]
    cases (rhs.evalLift m store).down <;> cases rest.eval m store <;> rfl

end

private theorem afterEquation (token : Port before .bool) (value : Port before t)
    (vs : NodeValues (model m) before) :
    emitValue (model m) env (.op (.after t)) (.cons token (.cons value .nil)) vs =
      (vs.get value).bind (fun _ => vs.get token) := by
  change (collect [.bool, t] _).elim none _ = _
  simp only [collect, portAt, Fin.cases_zero, Fin.cases_succ, Tuple.get]
  cases vs.get token <;> cases vs.get value <;> rfl

/-- A bottom incoming token cannot be restored by a following statement. -/
theorem bodyBottom (body : Body P vars outs) (ctx : Tuple (Port before) (.bool :: vars))
    (values : NodeValues (model m) before) (bottom : values.get (ctx.get .head) = none) :
    let b := body.lower (params := params) ctx
    (b.code.eval (model m) env values).get (b.refs.get .head) = none := by
  induction body generalizing before with
  | @assign vars t rhs =>
    let e := (expr rhs).lower (params := params) (tail ctx)
    let vs := e.code.eval (model m) env values
    change emitValue (model m) env (.op (.after t)) (.cons (e.code.lift (ctx.get .head)) e.refs) vs = none
    cases h : e.refs with
    | cons value rest =>
      cases rest
      rw [afterEquation]
      change (vs.get value).bind (fun _ => vs.get (e.code.lift (ctx.get .head))) = _
      rw [show vs.get (e.code.lift (ctx.get .head)) = none from (eval_lift _ _ _ _ _).trans bottom]
      cases vs.get value <;> rfl
  | project slots => exact bottom
  | seq first second ihFirst ihSecond =>
    let a := first.lower (params := params) ctx
    let b := second.lower (params := params) a.refs
    change ((a.code.append b.code).eval (model m) env values).get (b.refs.get .head) = none
    rw [eval_append]
    exact ihSecond a.refs _ (ihFirst ctx values bottom)

/-- With a realized input store, the lowered slice produces a token just
when the complete source slice succeeds, and preserves all output slots. -/
theorem bodyExact (body : Body P vars outs) (ctx : Tuple (Port before) (.bool :: vars))
    (values : NodeValues (model m) before) (token : (model m).Value .bool)
    (store : Tuple m.Value vars) (entry : Realizes (model m) values ctx (.cons token store)) :
    let b := body.lower (params := params) ctx
    let result := b.code.eval (model m) env values
    match body.source.runLoopFree m store with
    | none => result.get (b.refs.get .head) = none
    | some next => Realizes (model m) result b.refs (.cons token next) := by
  induction body generalizing before with
  | @assign vars t rhs =>
    cases ctx with
    | cons incoming ctx =>
      let e := (expr rhs).lower (params := params) ctx
      let vs := e.code.eval (model m) env values
      have rhsValue := exprExact m env rhs ctx values store (fun t p => entry t (.tail p))
      have oldValue : vs.get (e.code.lift incoming) = some token :=
        (eval_lift _ _ _ _ _).trans (entry _ .head)
      have flat : e.refs = .cons (e.refs.get .head) .nil := by
        cases e.refs with
        | cons _ rest => cases rest; rfl
      let nxt := emitValue (model m) env (.op (.after t)) (.cons (e.code.lift incoming) e.refs) vs
      have nextToken : nxt = (rhs.eval m store).map (fun _ => token) := by
        change emitValue _ _ _ _ _ = _
        rw [flat, afterEquation, oldValue]
        change (vs.get (e.refs.get .head)).bind (fun _ => some token) = _
        rw [rhsValue]
        cases rhs.eval m store <;> rfl
      simp only [Body.source, Stmt.runLoopFree, Body.lower, Token.tail, Tuple.get, Simple.Code.eval]
      cases test : rhs.eval m store with
      | none =>
        change nxt = none
        simpa only [test, Option.map_none] using nextToken
      | some value =>
        intro ty slot
        cases slot with
        | head =>
          change nxt = some token
          simpa only [test, Option.map_some] using nextToken
        | tail slot =>
          cases slot with
          | head => exact rhsValue.trans test
          | tail slot =>
            change (Tuple.cons (F := fun t => Option ((model m).Value t)) nxt vs).get
              (((e.code.liftRefs ctx).map fun _ p => Port.tail p).get slot) = some (store.get slot)
            rw [get_map]
            change vs.get ((e.code.liftRefs ctx).get slot) = _
            simp only [vs, Simple.Code.liftRefs, get_map, eval_lift]
            exact entry _ (.tail slot)
  | project slots =>
    cases ctx with
    | cons incoming ctx =>
      change Realizes (model m) values (.cons incoming (select ctx slots))
        (.cons token (select store slots))
      intro t p
      cases p with
      | head => exact entry _ .head
      | tail p =>
        change values.get ((select ctx slots).get p) = some ((select store slots).get p)
        rw [get_select, get_select]
        exact entry _ (.tail (slots.get p))
  | seq first second ihFirst ihSecond =>
    let a := first.lower (params := params) ctx
    let b := second.lower (params := params) a.refs
    let vs := a.code.eval (model m) env values
    simp only [Body.source, Stmt.runLoopFree, Body.lower, Simple.Build.thenBuild]
    rw [eval_append]
    have aExact := ihFirst ctx values store entry
    cases result : first.source.runLoopFree m store with
    | none =>
      exact bodyBottom m env second a.refs vs (by simpa only [result] using aExact)
    | some next =>
      exact ihSecond a.refs vs next (by simpa only [result] using aExact)

end Silmaril.SSA.PEG.Simple.Structured.Token.Proofs
