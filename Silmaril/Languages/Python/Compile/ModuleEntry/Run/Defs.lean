module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
public import Silmaril.Languages.Python.Core.Module.Defs

/-! # Compile and run a straight-line Python module -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Run

open Source (Scope)

def operator : BinaryOp → Core.Module.Operator
  | .add => .arithmetic .add
  | .floorDiv => .arithmetic .floorDiv
  | .equal => .equal
  | .notEqual => .notEqual

def expression {scope : Scope} : Operand scope → Core.Module.Expr
  | .integer value => .literal (.int value)
  | .boolean value => .literal (.bool value)
  | .none_ => .literal .none
  | .read name _ => .readGlobal name
  | .binary op left right => .binary (operator op) (expression left) (expression right)
  | .identityChain left links =>
    .identityChain (expression left) (links.attach.map fun link => (link.val.1, expression link.val.2))
termination_by operand => sizeOf operand
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have smaller := Core.Module.Identity.sizeOf_operand_lt link.property
      omega

def statement {scope : Scope} : Action scope → Core.Module.Stmt
  | .assign name _ value => .assignGlobal name (expression value)
  | .assertion condition => .assert (expression condition)

structure Compiled (source : Source.Module) where
  checked : Checked source
  initial : Core.Module.Globals

def Compiled.entry {source : Source.Module} (compiled : Compiled source) : Core.Module.Entry :=
  ⟨compiled.initial, compiled.checked.actions.map statement⟩

def compile (source : Source.Module) (initial : Core.Module.Globals := .empty) :
    Except Error (Compiled source) :=
  (check source).map fun checked => ⟨checked, initial⟩

def Compiled.run {source : Source.Module} (compiled : Compiled source) :
    List Core.Module.Label × Core.Module.State :=
  compiled.entry.run

end Silmaril.Languages.Python.Compile.ModuleEntry.Run
