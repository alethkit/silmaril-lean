module

import Silmaril.Languages.Starlark.Functions.Thms
meta import Silmaril.Languages.Starlark.Functions.Defs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs
meta import Silmaril.Languages.Starlark.Lists.Iteration.Defs

namespace Silmaril.Languages.Starlark.Functions

open Lists (State)
open Lists.Iteration (finishState)

private def slot (name : String) : Binding := ⟨.local, name⟩
private def read (name : String) : Lists.Expr := .read (.bound (slot name))
private def int (n : Int) : Lists.Expr := .scalar (.int n)
private def list (items : List Lists.Expr) : Lists.Expr := .list (operandList items)
private def set (name : String) (expr : Lists.Expr) : Body := .total (.atomic (.assign (slot name) expr))
private def ret (expr : Lists.Expr) : Body := .total (.ret expr)
private def seq (items : List Body) : Body := items.foldr Body.seq (.total (.atomic .pass))

private def appendProgram : Program := #[{
  signature := { positional := [⟨slot "target", none⟩, ⟨slot "value", none⟩] }
  locals := []
  free := []
  body := .total (.atomic (.eval (.append (read "target") (read "value")))) }]

private def appendCall (name : String) (value : Lists.Expr) : Body :=
  .call none (read "append") { positional := [read name, value] }

-- The inner break releases only its guard. The outer guard still blocks a
-- mutation attempted by a callee through a different name for the same list.
#guard
  let caller : State := { iterators := [99] }
  let code := seq [.define (slot "append") 0, set "xs" (list [int 1]), set "alias" (read "xs"),
    .forIn (slot "x") (read "xs")
      (.seq (.forIn (slot "y") (read "alias") .breakLoop) (appendCall "alias" (read "x")))]
  match run appendProgram code caller with
  | .error (.activeIteration address) after =>
    after.iterators == [99] &&
    (match after.bindingValue (slot "xs"), Lists.appendAt address (.scalar .none) after with
     | .ok (.list original), .ok _ _ => original == address
     | _, _ => false)
  | _ => false

-- Continue skips the first return. A subsequent return exits both the loop
-- body and its scope while retaining the effects of the previous calls.
#guard
  let caller : State := { iterators := [99] }
  let code := seq [.define (slot "append") 0, set "xs" (list [int 0, int 1, int 2]), set "events" (list []),
    .forIn (slot "x") (read "xs") (seq [
      .forIn (slot "y") (read "xs") (.seq (appendCall "events" (read "y")) .breakLoop),
      .branch (read "x") (ret (read "x")) .continueLoop]),
    ret (int 7)]
  match run appendProgram code caller with
  | .ok (.returned (.scalar (.int 1))) after =>
    after.iterators == [99] &&
    (match after.bindingValue (slot "events") with
     | .ok (.list address) =>
       match Lists.listElements address after with
       | .ok [.scalar (.int 0), .scalar (.int 0)] _ => true
       | _ => false
     | _ => false)
  | _ => false

-- A declaration begins with no enclosing loop, even if called from one.
#guard
  match runChecked #[{ signature := {}, locals := [], free := [], body := .continueLoop }]
      (.forIn (slot "x") (list []) (.call none (read "callee") {})) with
  | .error .continueOutsideLoop => true
  | _ => false

end Silmaril.Languages.Starlark.Functions
