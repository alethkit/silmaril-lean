module

import Silmaril.Languages.Starlark.Modules.Resolve.Assignment.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Assignment.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Assignment

open scoped Functions.Lowering.Quote
open Functions (Program)
open Lists

private def block : LexicalBlock where
  owned := ["slot", "i"]
  enclosing := ["get", "i", "arr"]
  globals := ["slot", "i", "get", "arr", "item"]

private def target : Functions.Lowering.Resolve.SourceExpr := starlark%[(slot, [get()[i], arr[slot]])]
private def rhs : CompExpr := .list ⟨starlark%[item], starlark%[item], .yield starlark%[item]⟩
private def emptyProgram : Program := {}

-- The two local rules distinguish owned names from captured names even
-- when both resolve to frame-local bindings. Both take priority over globals.
example : ReadResolves block "i" (.atom (.read (.bound (fileSlot "i")))) [fileSlot "i"] :=
  .owned (by decide)

example : ReadResolves block "get" (.atom (.read (.bound (fileSlot "get")))) [fileSlot "get"] :=
  .enclosing (by decide) (by decide)

-- The first iterable sees the module's item while the yield sees its fresh
-- local. Only the iterable read is retained as a capture input.
example : RhsResolves block rhs
    (.list ⟨[fileSlot "item"], .name (fileSlot "item"), .atom (.read (.bound (globalSlot "item"))),
      .yield (.atom (.read (.bound (fileSlot "item"))))⟩) [globalSlot "item"] :=
  .list (.read (by decide) (.global (by decide) (by decide) (by decide)))
    (.read (by decide) (.owned (by decide)))

-- Shape analysis marks the name leaf with the supplied write scope.
-- The receiver then index reads of the first store precede the second store.
private def checkScope (scope : Scope) (context : LexicalBlock) (slot : String → Binding) : Bool :=
  match elaboratePatternAssignment context.context scope target rhs emptyProgram with
  | .ok (result, _) =>
    match result.pattern with
    | .sequence [.name name, .sequence [.subscript .., .subscript ..]] =>
      name == slot "slot" && result.names == ["slot"] &&
        result.targetReads == ["get", "i", "arr", "slot"].map slot && result.rhsReads == [globalSlot "item"]
    | _ => false
  | .error _ => false

#guard checkScope .local block fileSlot
#guard checkScope .global { globals := block.globals } globalSlot

-- The normalized assignment grammar rejects non-target shapes, and the
-- quotation grammar has no field selection to normalize into a field leaf.
#guard
  match elaboratePatternAssignment block.context .local starlark%[(slot, get())] rhs emptyProgram with
  | .error .unsupportedAssignmentTarget => true
  | _ => false

/-- error: expected an unqualified Starlark identifier -/
#guard_msgs in
#check starlark%[slot.field]

-- Observe the earlier name and aliased list write in the failing module
-- state. The first store reads the newly assigned name as its index.
#guard
  let commands : List Command :=
    [.assign "xs" starlark%[[7]], .assign "alias" starlark%[xs], .assign "rows" starlark%[[0, 9, 10]],
     .assignTargetCompExpr starlark%[(i, alias[i], xs[8])]
       (.list ⟨starlark%[item], starlark%[rows], .yield starlark%[item]⟩)]
  match resolve commands with
  | .ok resolved =>
    match runCommands resolved.program (fun _ => none) resolved.source.commands (enter resolved.source {}) with
    | .error (.runtime (.indexRange 8 1)) state =>
      match state.bindingValue (globalSlot "i"), state.bindingValue (globalSlot "alias") with
      | .ok (.scalar (.int 0)), .ok (.list address) =>
        state.heap[address]?.map Cell.contents == some (.list [.scalar (.int 9)]) && state.iterators.isEmpty
      | _, _ => false
    | _ => false
  | _ => false

-- A local target shadows the module's i throughout the inner function.
-- The store reads that local and mutates an alias captured from its parent.
#guard
  let inner := Statement.seq
    (.assignTargetCompExpr starlark%[(i, alias[i])]
      (.list ⟨starlark%[i], starlark%[rows], .yield starlark%[i]⟩))
    (.ret (some starlark%[i]))
  let outer := Statement.seq (.assign "alias" starlark%[xs])
    (.seq (.define "inner" {} inner) (.ret (some starlark%[inner()])))
  let commands : List Command :=
    [.assign "i" starlark%[8], .assign "xs" starlark%[[7]], .assign "rows" starlark%[[0, 9]],
     .define "outer" {} outer, .assign "out" starlark%[(outer(), xs[0], i)]]
  match runModule commands (fun _ => none) {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "out" with
    | some (.tuple address) =>
      match state.heap[address]?.map Cell.contents with
      | some (.tuple values _) => values == [.scalar (.int 0), .scalar (.int 9), .scalar (.int 8)]
      | _ => false
    | _ => false
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Assignment
