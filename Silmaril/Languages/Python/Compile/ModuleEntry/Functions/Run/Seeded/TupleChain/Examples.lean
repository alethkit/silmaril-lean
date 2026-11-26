module

import Batteries.Data.Except
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain.Eval.Thms
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
meta import Silmaril.Languages.Python.Core.Module.TupleDispatch.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.TupleDispatch in
private def dispatchEvidence : Bool := Id.run do
  let (left, first) := Heap.empty.materialize [.bool true]
  let (right, second) := first.materialize [.int 2]
  let (empty, _) := second.materialize []
  let (joined, third) := concat second left right
  return joined == ⟨some 2, [.bool true, .int 2]⟩ &&
    third.objects == #[[.bool true], [.int 2], [.bool true, .int 2]] &&
    concat second empty left == (left, second) &&
    concat second left empty == (left, second) &&
    concat second empty empty == (empty, second) &&
    (BoundMethod.mk .eq left).invoke second (.list [.int 1]) == (.ok .notImplemented, second) &&
    (UnboundMethod.mk .eq).invoke second (.tuple left) (.list [.int 1]) == (.ok .notImplemented, second) &&
    (BoundMethod.mk .add left).invoke second (.list [.int 1]) == (.error .wrongArgument, second) &&
    !(equal left (.list [.int 1])) &&
    callUnbound second (some .stockTuple) .add (.list []) (.tuple [.int 3]) ==
      (.error (.wrongReceiver .add), ⟨#[[.bool true], [.int 2], [.int 3]]⟩) &&
    callUnbound second (some .noneValue) .add (.tuple [.int 3]) (.tuple [.int 4]) ==
      (.error (.missingAttribute .add), second)

#guard dispatchEvidence

private def intTuple (value : Int) : Source.Expr := .tuple [.integer value]

private def chain (middle : Int) : Source.Stmt :=
  let bound := Source.Expr.callWith (.attribute (intTuple 5) "__add__") [(.positional, .tuple [])]
  let unbound := Source.Expr.callWith (.attribute (.name "tuple") "__add__")
    [(.positional, intTuple middle), (.positional, .tuple [])]
  .assert_ (.comparison bound [(.eq, intTuple middle), (.eq, unbound)]) none

private def chainEvidence (space : Core.Module.SeededCall.Namespace) (middle : Int)
    (completion : Except ModuleFailure Unit) (reached : Nat) : Bool := Id.run do
  let source : Source.Module := ⟨[.assign "keep" (.integer 7), chain middle, .assign "tail" (.integer 9)]⟩
  let .ok compiled := Run.compile source | return false
  let [_, .assertTupleChain test, _] := compiled.instructions | return false
  let actual := TupleChain.evaluate (fun _ => tupleBinding space) test
  let heap : Core.Closure.Heap := ⟨1, fun address => if address = 0 then some (.int 23) else none⟩
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let outcome := run space compiled heap (lists := lists)
  let preserved := space.bindGlobal "keep" (.int 7)
  let expected := if completion.isOk then preserved.bindGlobal "tail" (.int 9) else preserved
  return actual.reached.length == reached && outcome.completion == completion &&
    outcome.residual.moduleGlobals == expected.moduleGlobals && outcome.residual.builtins == expected.builtins &&
    outcome.lists == lists && outcome.heap.next == 1 && (outcome.heap.contents 0).map seededValue == some (.int 23) &&
    outcome.calls.isEmpty

#guard chainEvidence (legacyTupleSeed .builtin) 5 (.ok ()) 3
#guard chainEvidence .empty 5 (.error (.raised (.runtime (.nameError "tuple")))) 3
#guard chainEvidence .empty 6 (.error (.raised (.assertionError .empty))) 2
#guard chainEvidence ((legacyTupleSeed .builtin).bindGlobal "tuple" .none) 5 (.error .unsupported) 3

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
