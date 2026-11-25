module

import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Defs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Syntax.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs

namespace Silmaril.Languages.Starlark.Functions

private def slot (name : String) : Binding := ⟨.local, name⟩
private def read (name : String) : Lists.Expr := .read (.bound (slot name))
private def int (n : Int) : Lists.Expr := .scalar (.int n)
private def list (values : List Int) : Lists.Expr := .list (operandList (values.map int))
private def set (name : String) (value : Lists.Expr) : Body := .total (.atomic (.assign (slot name) value))
private def append (name : String) (value : Lists.Expr) : Body :=
  .total (.atomic (.eval (.append (read name) value)))

private def range (args : List Int) : Lowering.Expr :=
  .callPos (.atom (.builtin .range)) (args.map fun n => .atom (int n))

private def program : Program := #[
  ⟨{ positional := [⟨slot "xs", none⟩] }, [], [],
    .seq (append "xs" (int 3)) (.returnExpr (.atom (read "xs")))⟩,
  ⟨{ positional := [⟨slot "xs", none⟩] }, [], [],
    .seq (append "xs" (int 3)) (.returnExpr (range [10, 3, -2]))⟩]

private def iterable : Lowering.Expr :=
  .callPos (.atom (read "prepare")) [.atom (read "xs")]

private def execute (loop : Body) (owned : List String := []) :=
  let setup := [Body.define (slot "prepare") 0, Body.define (slot "prepareRange") 1,
    set "xs" (list [1, 2]), set "alias" (read "xs"),
    set "seen" (list []), set "x" (int 7)]
  let initial : Lists.State := { heap := #[⟨.list [], false⟩], iterators := [0] }
  runChecked program (setup.foldr Body.seq loop)
    (owned.foldl (fun state name => state.allocateSlot (slot name)) initial)

private def hasList (state : Lists.State) (name : String) (expected : List Int) : Bool :=
  match state.bindingValue (slot name) with
  | .ok (.list address) =>
    match Lists.listElements address state with
    | .ok values _ => decide (values = expected.map fun n => .scalar (.int n))
    | _ => false
  | _ => false

private def visit : Body := append "seen" (read "x")

private def hasInt (state : Lists.State) (name : String) (expected : Int) : Bool :=
  match state.bindingValue (slot name) with
  | .ok (.scalar (.int value)) => value == expected
  | _ => false

-- The operand mutates its own returned list once. The snapshot includes the new item.
#guard
  match execute (.forInExpr (slot "x") iterable visit) with
  | .ok (.ok .next final) =>
    final.iterators == [0] && hasList final "xs" [1, 2, 3] && hasList final "seen" [1, 2, 3]
  | _ => false

-- The inner call mutates the list, then the enclosing len fails before there is a loop target write.
#guard
  let failure := Lowering.Expr.callPos (.atom (.builtin .len))
    [.logical .and iterable (.atom (int 9))]
  match execute (.forInExpr (slot "x") failure visit) with
  | .ok (.error (.builtinType .len (.scalar (.int 9))) final) =>
    final.iterators == [0] && hasList final "xs" [1, 2, 3] && hasList final "seen" [] &&
      match final.bindingValue (slot "x") with
      | .ok (.scalar (.int 7)) => true
      | _ => false
  | _ => false

-- Successful acquisition blocks alias writes. Body failure releases only the loop's own guard.
#guard
  match execute (.forInExpr (slot "x") iterable (append "alias" (int 4))) with
  | .ok (.error (.activeIteration address) final) =>
    final.iterators == [0] && hasList final "xs" [1, 2, 3] &&
      match final.bindingValue (slot "xs"), Lists.appendAt address (.scalar (.int 4)) final with
      | .ok (.list original), .ok _ amended => original == address && hasList amended "xs" [1, 2, 3, 4]
      | _, _ => false
  | _ => false

#guard
  match execute (.forInExpr (slot "x") iterable (.returnExpr (.atom (read "x")))) with
  | .ok (.ok (.returned (.scalar (.int 1))) final) =>
    final.iterators == [0] && hasList final "xs" [1, 2, 3]
  | _ => false

#guard
  let invalid := Lowering.Expr.call (.atom (.builtin .len)) []
    [("x", .atom (int 1)), ("x", .atom (int 2))] none none
  let skipped := Lowering.Expr.logical .or (.atom (int 1)) invalid
  match execute (.forInExpr (slot "x") skipped .breakLoop), execute (.forInExpr (slot "x") iterable .breakLoop) with
  | .error (.duplicateExplicitKeyword "x"), .ok (.ok .next _) => true
  | _, _ => false

#guard
  match execute (.forInExpr (slot "x") (range [0]) visit) with
  | .ok (.ok .next final) =>
    final.iterators == [0] && hasList final "seen" [] && hasInt final "x" 7
  | _ => false

-- The operand closure runs once and both paths visit the same slice.
#guard
  let operand := Lowering.Expr.slice
    (.callPos (.atom (read "prepareRange")) [.atom (read "xs")])
    (.atom (int 1)) (.atom (.scalar .none)) (.atom (int 2))
  let body := Body.seq visit (.seq .continueLoop (append "seen" (int 99)))
  let check := fun loop => match execute loop with
    | .ok (.ok .next final) =>
      final.iterators == [0] && hasList final "xs" [1, 2, 3] && hasList final "seen" [8, 4] &&
        hasInt final "x" 4
    | _ => false
  check (.forInExpr (slot "x") operand body) &&
    check (Lowering.lowerForIn (slot "x") operand body).code

-- A failing slice operand retains the range-producing call's effect and
-- skips both the binder write and the loop body in either path.
#guard
  let operand := Lowering.Expr.slice
    (.callPos (.atom (read "prepareRange")) [.atom (read "xs")])
    (.atom (.scalar .none)) (.atom (.scalar .none)) (.atom (int 0))
  let check := fun loop => match execute loop with
    | .ok (.error .zeroSliceStride final) =>
      final.iterators == [0] && hasList final "xs" [1, 2, 3] && hasList final "seen" [] &&
        hasInt final "x" 7
    | _ => false
  check (.forInExpr (slot "x") operand visit) &&
    check (Lowering.lowerForIn (slot "x") operand visit).code

-- A huge exact range can exit after a single iteration on either break or return.
#guard
  let huge := range [11, 11 + 10^24]
  match execute (.forInExpr (slot "x") huge (.seq visit .breakLoop)),
      execute (.forInExpr (slot "x") huge (.returnExpr (.atom (read "x")))) with
  | .ok (.ok .next stopped), .ok (.ok (.returned (.scalar (.int 11))) returned) =>
    stopped.iterators == [0] && returned.iterators == [0] && hasList stopped "seen" [11] &&
      hasInt stopped "x" 11
  | _, _ => false

-- The range acquires no guard and leaves the enclosing list guard active.
-- An alias write fails, preserving the first range step's other write.
#guard
  let inner := Body.forInExpr (slot "x") (range [10, 3, -2])
    (.seq visit (append "alias" (int 99)))
  match execute (.forIn (slot "outer") (read "xs") inner) with
  | .ok (.error (.activeIteration address) final) =>
    final.iterators == [0] && hasList final "seen" [10] && hasList final "xs" [1, 2] &&
      hasInt final "outer" 1 && hasInt final "x" 10 &&
      match Lists.appendAt address (.scalar (.int 99)) final with
      | .ok _ amended => hasList amended "xs" [1, 2, 99]
      | _ => false
  | _ => false

-- A mismatch preserves the earlier iteration and operand effects, and it
-- neither overwrites the earlier binder slots nor visits later items.
#guard
  let flat := Lists.Iteration.LoopTarget.unpack [slot "x", slot "y"]
  let atom := fun n => Lowering.Expr.atom (int n)
  let rows := Lowering.Expr.list [.tuple [atom 1, atom 2], .list [atom 3], .tuple [atom 5, atom 6]]
  let operand := Lowering.Expr.logical .and iterable rows
  match execute (.forInExpr flat operand visit) ["x", "y"],
      execute (Lowering.lowerForIn flat operand visit).code ["x", "y"] with
  | .ok (.error (.unpackArity 2 1) final), .ok (.error (.unpackArity 2 1) lowered) =>
    final.iterators == [0] && lowered.iterators == [0] &&
      hasInt final "x" 1 && hasInt final "y" 2 && hasList final "seen" [1] &&
      hasList final "xs" [1, 2, 3] && decide (final.heap = lowered.heap) &&
      -- The outer iterable list is the final allocation, made after the rows.
      match Lists.appendAt (final.heap.size - 1) (.scalar .none) final with
      | .ok _ _ => true
      | _ => false
  | _, _ => false

-- The exact descriptor count rejects the item before the range is collected.
#guard
  let check := fun item expected =>
    match execute (.forInExpr (.unpack [slot "x", slot "y"]) (.list [item]) visit) ["x", "y"] with
    | .ok (.error error final) =>
      error == expected && final.iterators == [0] && hasInt final "x" 7 &&
        hasList final "seen" [] &&
        match final.bindingValue (slot "y") with
        | .error (.uninitialized name) => name == slot "y"
        | _ => false
    | _ => false
  check (range [10^24]) (.unpackArity 2 (10^24)) &&
    check (.atom (int 9)) (.unpackTarget (.scalar (.int 9)))

-- A child mismatch keeps writes to earlier siblings in the same iteration.
-- The two matched heaps include the partially updated owned cells.
#guard
  let target : Lists.Iteration.LoopTarget := .sequence [
    .name (slot "x"), .unpack [slot "y", slot "z"], .name (slot "w")]
  let atom := fun n => Lowering.Expr.atom (int n)
  let first := Lowering.Expr.tuple [atom 1, .list [atom 2, atom 3], atom 4]
  let check := fun middle error x =>
    let operand := Lowering.Expr.logical .and iterable (.list [first, middle, first])
    let owned := ["x", "y", "z", "w"]
    match execute (.forInExpr target operand visit) owned,
        execute (Lowering.lowerForIn target operand visit).code owned with
    | .ok (.error nativeError final), .ok (.error loweredError lowered) =>
      nativeError == error && loweredError == error &&
        final.iterators == [0] && lowered.iterators == [0] &&
        hasInt final "x" x && hasInt final "y" 2 && hasInt final "z" 3 && hasInt final "w" 4 &&
        hasList final "seen" [1] && hasList final "xs" [1, 2, 3] &&
        decide (final.heap = lowered.heap)
    | _, _ => false
  check (.list [atom 5, .list [atom 6], atom 7]) (.unpackArity 2 1) 5 &&
    check (.list [atom 5, .list [atom 6, atom 7]]) (.unpackArity 3 2) 1 &&
    check (.list [atom 5, range [10^24], atom 7]) (.unpackArity 2 (10^24)) 5

end Silmaril.Languages.Starlark.Functions
