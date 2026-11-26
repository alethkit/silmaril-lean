module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain.Eval.Defs
public import Silmaril.Languages.Python.Core.Module.TupleDispatch.Thms

public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain

open Core.Module.TupleDispatch (Failure Heap Object TypeBinding)

theorem scan_error {scope : Source.Scope} (lookup : Unit → Option TypeBinding)
    (heap reached : Heap) (left : Object) (operand : TupleOperand scope) (rest : List (TupleOperand scope))
    (error : Failure) (failed : evaluateOperand lookup heap operand = (.error error, reached)) :
    scan lookup heap left (operand :: rest) = ⟨.error error, reached, [.error error]⟩ := by
  simp [scan, failed]

theorem scan_false {scope : Source.Scope} (lookup : Unit → Option TypeBinding)
    (heap reached : Heap) (left right : Object) (operand : TupleOperand scope)
    (rest : List (TupleOperand scope))
    (evaluated : evaluateOperand lookup heap operand = (.ok right, reached)) (different : equal left right = false) :
    scan lookup heap left (operand :: rest) = ⟨.ok false, reached, [.ok right]⟩ := by
  simp [scan, evaluated, different]

theorem scan_next {scope : Source.Scope} (lookup : Unit → Option TypeBinding)
    (heap reached : Heap) (left right : Object) (operand : TupleOperand scope)
    (rest : List (TupleOperand scope))
    (evaluated : evaluateOperand lookup heap operand = (.ok right, reached)) (same : equal left right = true) :
    scan lookup heap left (operand :: rest) =
      let tail := scan lookup reached right rest
      { tail with reached := .ok right :: tail.reached } := by
  simp [scan, evaluated, same]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain
