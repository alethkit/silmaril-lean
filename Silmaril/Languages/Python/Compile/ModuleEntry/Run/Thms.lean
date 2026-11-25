module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Run.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Thms
public import Silmaril.Languages.Python.Core.Module.Thms

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Run

theorem global_read {scope : Source.Scope} {name : Source.Name} (reference : GlobalReference scope name) :
    expression (.read name reference) = .readGlobal name := rfl

theorem global_write {scope : Source.Scope} {name : Source.Name} (reference : GlobalReference scope name)
    (value : Operand scope) : statement (.assign name reference value) = .assignGlobal name (expression value) := rfl

theorem eval_conditionalResult {scope : Source.Scope} (globals : Core.Module.Globals) (operand : Operand scope) :
    (expression operand.conditionalResult).eval globals = (expression operand).eval globals := by
  cases operand with
  | boolean value => cases value <;> rfl
  | _ => rfl

theorem eval_booleanResult {scope : Source.Scope} (globals : Core.Module.Globals) (value : Bool) :
    (expression (Operand.booleanResult (scope := scope) value)).eval globals = .ok (.bool value) :=
  eval_conditionalResult globals (.boolean value)

theorem Compiled.starts_with {source : Source.Module} (compiled : Compiled source) :
    compiled.entry.start = .running compiled.initial (compiled.checked.actions.map statement) := rfl

theorem Compiled.run_finishes {source : Source.Module} (compiled : Compiled source) :
    ∃ observation, compiled.run.2 = .finished observation :=
  compiled.entry.run_finishes

theorem Compiled.finishes_iff {source : Source.Module} (compiled : Compiled source)
    {log : List Core.Module.Label} {outcome : Semantics.Operational.Outcome Core.Module.Observation} :
    Core.Module.labelled.Finishes compiled.entry.start log outcome ↔
      ∃ observation, compiled.run = (log, .finished observation) ∧ outcome = .returned observation :=
  Core.Module.Entry.finishes_iff

end Silmaril.Languages.Python.Compile.ModuleEntry.Run
