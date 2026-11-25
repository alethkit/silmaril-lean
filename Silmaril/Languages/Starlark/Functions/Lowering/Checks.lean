module

import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Defs
meta import Silmaril.Languages.Starlark.Functions.Defs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State)

deriving instance DecidableEq for Except

private def slot (name : String) : Binding := ⟨.local, name⟩
private def read (name : String) : Lists.Expr := .read (.bound (slot name))
private def int (n : Int) : Lists.Expr := .scalar (.int n)
private def list (items : List Lists.Expr) : Lists.Expr := .list (operandList items)
private def param (name : String) (defaultExpr : Option Lists.Expr := none) : Parameter :=
  ⟨slot name, defaultExpr⟩
private def set (name : String) (expr : Lists.Expr) : Body := .total (.atomic (.assign (slot name) expr))
private def effect (expr : Lists.Expr) : Body := .total (.atomic (.eval expr))
private def ret (expr : Lists.Expr) : Body := .total (.ret expr)
private def seq (items : List Body) : Body := items.foldr Body.seq (.total (.atomic .pass))

private def program : Program := #[
  ⟨{ positional := [param "events", param "value"] }, [], [],
    .seq (effect (.append (read "events") (read "value"))) (ret (read "value"))⟩,
  ⟨{ positional := [param "events"] }, [], [⟨slot "collect", slot "collect"⟩],
    .seq (effect (.append (read "events") (int 0))) (ret (read "collect"))⟩,
  ⟨{ positional := [param "a", param "b", param "c" (int 0), param "d" (int 0)] }, [], [],
    ret (.tuple (operandList (["a", "b", "c", "d"].map read)))⟩]

private def setup : Body := seq [
  .define (slot "collect") 2, .define (slot "dispatch") 1, .define (slot "mark") 0,
  set "events" (list []), set "out" (int 7)]

private def mark (value : Lists.Expr) : Expr :=
  .callPos (.atom (read "mark")) [.atom (read "events"), .atom value]

private def frame (lowered : Lowered) : State :=
  (slot "collect" :: lowered.temporaries).foldl State.allocateSlot {}

-- The callee and all four argument classes execute in source order.
-- In particular, an atomic argument runs before a later nested call.
#guard
  let dict := Lists.Code.dict (.entry .noEntries (.string "d") (int 4))
  let expr := Expr.call (.callPos (.atom (read "dispatch")) [.atom (read "events")])
    [.atom (.append (read "events") (int 1))] [("c", mark (int 2))]
    (some (mark (list [int 3]))) (some (mark dict))
  let lowered := lower expr (slot "out")
  match run program (.seq setup lowered.code) (frame lowered) with
  | .ok .next state =>
    match state.bindingValue (slot "out"), state.bindingValue (slot "events") with
    | .ok (.tuple out), .ok (.list events) =>
      match Lists.tupleElements out state, Lists.listElements events state with
      | .ok [.scalar .none, .scalar (.int 3), .scalar (.int 2), .scalar (.int 4)] _,
        .ok [.scalar (.int 0), .scalar (.int 1), .scalar (.int 2), .list _, .dict _] _ => true
      | _, _ => false
    | _, _ => false
  | _ => false

private def len (arg : Expr) : Expr := .callPos (.atom (.builtin .len)) [arg]

-- Lowering feeds the same loop body language and keeps unselected code lazy.
#guard
  let bad := len (.atom (int 42))
  let expr := Expr.branch (len (.atom (list [int 8])))
    (.logical .or (len (.atom (list [int 9]))) bad) bad
  let lowered := lower expr (slot "out")
  let code := Body.forIn (slot "i") (list [int 1]) lowered.code
  match run #[] code (frame lowered) with
  | .ok .next state => decide (state.bindingValue (slot "out") = .ok (.scalar (.int 1))) &&
    state.iterators.isEmpty
  | _ => false

-- A failing right operand preserves earlier effects and the old destination.
#guard
  let lowered := lower (.logical .and (.atom (int 1)) (len (mark (int 5)))) (slot "out")
  match run program (.seq setup lowered.code) (frame lowered) with
  | .error (.builtinType .len (.scalar (.int 5))) state =>
    decide (state.bindingValue (slot "out") = .ok (.scalar (.int 7))) &&
    (match state.bindingValue (slot "events") with
     | .ok (.list events) =>
       match Lists.listElements events state with
       | .ok [.scalar (.int 5)] _ => true
       | _ => false
     | _ => false)
  | _ => false

#guard
  let first := lower (len (.atom (list []))) (slot "out") 10
  let second := lower (len (.atom (list []))) (slot "out") first.next
  first.temporaries == [temporary 10, temporary 11] &&
    second.temporaries == [temporary 12, temporary 13] && second.next == 14

#guard
  let invalid := Expr.call (.atom (.builtin .len)) [] [("x", .atom (int 1)), ("x", .atom (int 2))]
    none none
  let lowered := lower (.branch (.atom (int 1)) (.atom (int 2)) invalid) (slot "out")
  match runChecked #[] lowered.code (frame lowered) with
  | .error (.duplicateExplicitKeyword "x") => true
  | _ => false

end Silmaril.Languages.Starlark.Functions.Lowering
