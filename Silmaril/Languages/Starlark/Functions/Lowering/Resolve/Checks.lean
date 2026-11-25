module

import Silmaril.Languages.Starlark.Functions.Denotation.Defs
import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs

namespace Silmaril.Languages.Starlark.Functions.Lowering.Resolve

private def name (text : String) : SourceExpr := .scalar (.read text)
private def int (value : Int) : SourceExpr := .scalar (.int value)
private def global (text : String) : Binding := ⟨.global, text⟩
private def destination : Binding := global "out"

private def invalidLen : SourceExpr := .call (name "len") [int 9] [] none none

-- (len(*items, **keywords) or len(9)) if True else len(9)
private def expression : SourceExpr :=
  .conditional (name "True")
    (.logical .or (.call (name "len") [] [] (some (name "items")) (some (name "keywords"))) invalidLen)
    invalidLen

private def context : Context := { globals := ["items", "keywords"] }

private def initial : Lists.State :=
  { heap := #[⟨.tuple [.string "abc"] none, false⟩, ⟨.dict [], false⟩]
    bindings := fun b =>
      if b = global "items" then some (.tuple 0)
      else if b = global "keywords" then some (.dict 1)
      else none }

-- Resolve names, lower to the shared store and execute through the checked entry point.
#guard
  match resolve context expression with
  | .ok resolved =>
    match runChecked #[] (lower resolved destination).code initial with
    | .ok (.ok .next state) =>
      match state.bindingValue destination with
      | .ok (.scalar (.int 3)) => decide (state.heap = initial.heap)
      | _ => false
    | _ => false
  | .error _ => false

-- A local shadows a global and a built-in even if it has no value at entry.
#guard
  match resolve { locals := ["len"], globals := ["len"] } invalidLen with
  | .ok resolved =>
    let state : Lists.State := ({} : Lists.State).write (global "len") (.builtin .len)
    match runChecked #[] (lower resolved destination).code state with
    | .ok (.error (.uninitialized ⟨.local, "len"⟩) _) => true
    | _ => false
  | .error _ => false

#guard
  match resolve { globals := ["len"] } (name "len") with
  | .ok (.atom (.read (.bound ⟨.global, "len"⟩))) => true
  | _ => false

-- Resolution checks all branches, including those skipped during evaluation.
#guard
  match resolve {} (.conditional (name "True") (int 0) (name "missing")) with
  | .error (.lexical (.undefinedName "missing")) => true
  | _ => false

#guard
  match resolve {} (.scalar (.logical .and (.read "False") (.binary .add (.int 1) (.int 2)))) with
  | .error (.unsupportedBinary .add) => true
  | _ => false

#guard
  match resolve {} (.scalar (.unary .not (.read "True"))) with
  | .error (.unsupportedUnary .not) => true
  | _ => false

#guard
  match resolve { locals := ["$expr0"] } (name "$expr0") with
  | .error (.reservedName "$expr0") => true
  | _ => false

-- The checked executor still rejects repeated explicit keywords in unreachable code.
#guard
  let call := SourceExpr.call (name "len") [] [("x", int 1), ("x", int 2)] none none
  match resolve {} (.conditional (name "True") (int 0) call) with
  | .ok resolved =>
    match runChecked #[] (lower resolved destination).code with
    | .error (.duplicateExplicitKeyword "x") => true
    | _ => false
  | .error _ => false

end Silmaril.Languages.Starlark.Functions.Lowering.Resolve
