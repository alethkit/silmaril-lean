module

import Silmaril.Languages.Starlark.Functions.Denotation.Defs
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Lean.Elab.GuardMsgs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs

namespace Silmaril.Languages.Starlark.Functions.Lowering

open scoped Quote
open Resolve (resolve)

private def name (text : String) : Resolve.SourceExpr := .scalar (.read text)
private def int (value : Int) : Resolve.SourceExpr := .scalar (.int value)

-- The grammar keeps the nested callee and all operand classes, including a trailing comma.
example :
    starlark%[choose()(1, key = value(), *args, **kwargs,)] =
      Resolve.SourceExpr.call (.call (name "choose") [] [] none none) [int 1]
        [("key", .call (name "value") [] [] none none)] (some (name "args")) (some (name "kwargs")) :=
  rfl

-- Calls bind tighter than the logical operators, and conditionals associate to the right.
example :
    starlark%[f() or a and b if flag else 2 if other else -3] =
      Resolve.SourceExpr.conditional (name "flag")
        (.logical .or (.call (name "f") [] [] none none) (.logical .and (name "a") (name "b")))
        (.conditional (name "other") (int 2) (int (-3))) :=
  rfl

-- Run the quoted source through resolution and lowering. Both invalid len calls are skipped.
#guard
  let initial : Lists.State :=
    { heap := #[⟨.tuple [.string "abc"] none, false⟩, ⟨.dict [], false⟩]
      bindings := fun b =>
        if b = ⟨.global, "items"⟩ then some (.tuple 0)
        else if b = ⟨.global, "keywords"⟩ then some (.dict 1)
        else none }
  let destination : Binding := ⟨.global, "out"⟩
  match resolve { globals := ["items", "keywords"] }
      starlark%[(len(*items, **keywords) or len(9)) if True else len(9)] with
  | .ok resolved =>
    match runChecked #[] (lower resolved destination).code initial with
    | .ok (.ok .next state) =>
      match state.bindingValue destination with
      | .ok (.scalar (.int 3)) => decide (state.heap = initial.heap)
      | _ => false
    | _ => false
  | .error _ => false

example : starlark%[len("é",)] =
    Resolve.SourceExpr.call (name "len") [.string "é"] [] none none := rfl

example : starlark%[type] = name "type" := rfl

example : starlark%[()] = Resolve.SourceExpr.tuple [] := rfl
example : starlark%[(x,)] = Resolve.SourceExpr.tuple [name "x"] := rfl
example : starlark%[(x)] = name "x" := rfl
example : starlark%[{}] = Resolve.SourceExpr.dict [] := rfl

/--
@ +1:25...26
error: binary '+' is outside the Starlark expression quotation
-/
#guard_msgs (error, positions := true, drop info) in
#check starlark%[len("x" + "y")]

example : starlark%[[pick(1), [2],][key()][0]] =
    Resolve.SourceExpr.index
      (.index (.list [.call (name "pick") [int 1] [] none none, .list [int 2]])
        (.call (name "key") [] [] none none)) (int 0) := rfl

example : starlark%[xs[:]] = Resolve.SourceExpr.slice (name "xs") none none none := rfl
example : starlark%[xs[::]] = Resolve.SourceExpr.slice (name "xs") none none none := rfl
example : starlark%[xs[::-2][0]] =
    Resolve.SourceExpr.index (.slice (name "xs") none none (some (int (-2)))) (int 0) := rfl
example : starlark%[xs[-1 : None :]] =
    Resolve.SourceExpr.slice (name "xs") (some (int (-1))) (some (name "None")) none := rfl

/--
@ +1:27...34
error: keyword arguments must precede '*'
-/
#guard_msgs (positions := true) in
#check starlark%[f(1, *xs, key = 2)]

/--
@ +1:25...26
error: no argument may follow '**'
-/
#guard_msgs (positions := true) in
#check starlark%[f(**kw, 1)]

/--
@ +1:26...27
error: duplicate explicit keyword 'x'
-/
#guard_msgs (positions := true) in
#check starlark%[f(x = 1, x = 2)]

/--
@ +1:17...22
error: expected a double-quoted string without escapes
-/
#guard_msgs (positions := true) in
#check starlark%["a\n"]

end Silmaril.Languages.Starlark.Functions.Lowering
