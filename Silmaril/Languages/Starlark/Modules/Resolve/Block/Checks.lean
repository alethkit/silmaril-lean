module

import Silmaril.Languages.Starlark.Modules.Resolve.Block.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Block

open scoped Functions.Lowering.Quote
open Lists

private def target : Functions.Lowering.Resolve.SourceExpr := starlark%[(x, [buffer[i], y])]
private def rhs : CompExpr := .list ⟨starlark%[item], starlark%[rows], .yield starlark%[item]⟩
private def assignment : Statement := .assignTargetCompExpr target rhs

private theorem targetNames (scope : Scope) : TargetBinders scope target ["x", "y"] :=
  ⟨_, .tuple (.cons (.name "x")
    (.cons (.list (.cons (.subscript starlark%[buffer] starlark%[i]) (.cons (.name "y") .nil))) .nil))⟩

-- The read in the first command and the store operands declare nothing.
example : moduleBlock [.eval starlark%[i], .assignTargetCompExpr target rhs] =
    ⟨⟨[], ["x", "y"]⟩, .global⟩ :=
  moduleBlock_eq (.cons (.eval _) (.cons (.pattern (targetNames .global)) .nil))

private def body : Statement :=
  .seq (.eval starlark%[x]) (.branch starlark%[False] assignment (.assign "y" starlark%[2]))

private def signature : SourceSignature :=
  { positional := [⟨"i", none⟩, ⟨"x", none⟩] }

private theorem bodyNames : BodyBinders body ["x", "y", "y"] :=
  .seq (.eval _) (.branch (.pattern (targetNames .local)) (.assign _ _))

private theorem locals : LocalBinders ["i", "x"] ["x", "y", "y"] ["y"] :=
  .skip (by decide) (.keep (by decide) .nil)

-- Both branches supply binders. Repeated y shares a local slot and
-- assigning x reuses the parameter. Captured and global names stay visible.
example : collectFunctionLayout ⟨["buffer", "i"], ["rows", "x", "y"]⟩ signature body =
    .ok ⟨["y"], ⟨⟨["i", "x", "y", "buffer", "i"], ["rows", "x", "y"]⟩, .local⟩⟩ :=
  collectFunctionLayout_eq _ (.signature none none (.cons rfl (.cons rfl .nil)) .nil) bodyNames locals

example : Assignment.ReadResolves ⟨["i", "x", "y"], ["buffer", "x"], ["x", "y"]⟩ "x"
    (.atom (.read (.bound (fileSlot "x")))) [fileSlot "x"] :=
  owned_read ⟨["buffer", "x"], ["x", "y"]⟩ locals (.inl (by decide))

example : Assignment.ReadResolves ⟨["i", "x", "y"], ["buffer", "x"], ["x", "y"]⟩ "y"
    (.atom (.read (.bound (fileSlot "y")))) [fileSlot "y"] :=
  owned_read ⟨["buffer", "x"], ["x", "y"]⟩ locals (.inr (by decide))

-- Even a skipped assignment in a later branch establishes a local for
-- the whole function. The earlier read fails in the local slot.
#guard
  let before := Statement.seq (.eval starlark%[x])
    (.branch starlark%[False] assignment .pass)
  let commands : List Command :=
    [.assign "x" starlark%[8], .assign "i" starlark%[0], .assign "buffer" starlark%[[7]],
     .assign "rows" starlark%[[0, [9, 10]]], .define "before" {} before, .eval starlark%[before()]]
  match runModule commands (fun _ => none) {} with
  | .ok (.error (.runtime (.uninitialized slot)) _) => slot == fileSlot "x"
  | _ => false

private def closureModule : List Command :=
  let inner := Statement.seq (.setIndex starlark%[alias] starlark%[1] starlark%[i])
    (.seq (.assignTargetCompExpr starlark%[(i, alias[i])] rhs) (.ret (some starlark%[i])))
  let outer := Statement.seq (.define "inner" { positional := [⟨"i", none⟩] } inner)
    (.ret (some starlark%[inner]))
  [.assign "i" starlark%[8], .assign "xs" starlark%[[7, 0]], .assign "rows" starlark%[[0, 9]],
   .define "outer" { positional := [⟨"alias", none⟩] } outer,
   .assign "mover" starlark%[outer(xs)], .assign "out" starlark%[(mover(5), xs[0], xs[1], i)]]

-- The emitted inner declaration captures its parent's parameter and the
-- module iterable. Its reassigned parameter keeps its original slot.
#guard
  match resolve closureModule with
  | .ok resolved =>
    match resolved.program[0]? with
    | some inner =>
      inner.locals.isEmpty &&
        inner.free.map Functions.FreeName.source == [fileSlot "alias", globalSlot "rows"] &&
        resolved.source.globals == ["i", "xs", "rows", "outer", "mover", "out"]
    | none => false
  | .error _ => false

-- Invoke the escaped closure after the parent returns. The first store
-- observes the shadowing parameter, and the mixed target changes the alias.
#guard
  match runModule closureModule (fun _ => none) {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "out" with
    | some (.tuple address) =>
      match state.heap[address]?.map Cell.contents with
      | some (.tuple values _) =>
        values == [.scalar (.int 0), .scalar (.int 9), .scalar (.int 5), .scalar (.int 8)]
      | _ => false
    | _ => false
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Block
