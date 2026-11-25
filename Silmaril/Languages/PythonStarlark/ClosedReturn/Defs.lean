module

public import Silmaril.Languages.Python.Core.Defs
public import Silmaril.Languages.Starlark.Denotation.Defs
public import Silmaril.Languages.Starlark.Operational.Defs

@[expose] public section

/-! # Shared syntax for closed arithmetic return bodies -/

namespace Silmaril.Languages.PythonStarlark.ClosedReturn

open Semantics.Operational

inductive Op where
  | add
  | floorDiv
  deriving DecidableEq, Repr

def Op.python : Op → Languages.Python.Core.BinOp
  | .add => .add
  | .floorDiv => .floorDiv

def Op.starlark : Op → Starlark.BinaryOp
  | .add => .add
  | .floorDiv => .floorDiv

inductive Expr (Literal : Type) where
  | literal (value : Literal)
  | binary (op : Op) (left right : Expr Literal)

structure Body (Literal : Type) where
  value : Expr Literal

abbrev IntBody := Body Int

variable {Literal Ref : Type}

/-- Python lowering preserves grouping and emits only integer core expressions. -/
def Expr.python (literal : Literal → Int) : Expr Literal → Languages.Python.Core.Expr
  | .literal value => .int (literal value)
  | .binary op left right => .binary op.python (left.python literal) (right.python literal)

def IntBody.python (body : IntBody) : Languages.Python.Core.Body :=
  ⟨body.value.python id⟩

/-- Starlark lowering preserves grouping and leaves name interpretation to resolution. -/
def Expr.starlark (literal : Literal → Starlark.Expr Ref) : Expr Literal → Starlark.Expr Ref
  | .literal value => literal value
  | .binary op left right => .binary op.starlark (left.starlark literal) (right.starlark literal)

def IntBody.starlark (body : IntBody) : Starlark.SourceStmt :=
  .ret (some (body.value.starlark .int))

/-- Coercible Python literals. Starlark keeps the two scalar types distinct. -/
inductive NumericLiteral where
  | int (value : Int)
  | bool (value : Bool)

def NumericLiteral.pythonInt : NumericLiteral → Int
  | .int n => n
  | .bool b => b.toNat

def NumericLiteral.starlark : NumericLiteral → Starlark.SourceExpr
  | .int n => .int n
  | .bool b => .read (if b then "True" else "False")

/-- The expected result of resolving these literals in the empty context. -/
def NumericLiteral.starlarkResolved : NumericLiteral → Starlark.ResolvedExpr
  | .int n => .int n
  | .bool b => .read (.predeclared (.bool b))

/-- The Boolean adapter requires an arithmetic operation at the root, so every
Boolean literal is a numeric operand and the result cannot be a bare Boolean. -/
structure NumericBody where
  op : Op
  left : Expr NumericLiteral
  right : Expr NumericLiteral

def NumericBody.body (body : NumericBody) : Body NumericLiteral :=
  ⟨.binary body.op body.left body.right⟩

def NumericBody.python (body : NumericBody) : Languages.Python.Core.Body :=
  ⟨body.body.value.python NumericLiteral.pythonInt⟩

def NumericBody.starlark (body : NumericBody) : Starlark.SourceStmt :=
  .ret (some (body.body.value.starlark NumericLiteral.starlark))

/-- The common observations include agreement cases and separately classified
outcomes that can invalidate agreement. -/
inductive Observation where
  | returned (value : Int)
  | zeroDivision
  | rejected
  | unsupported
  | diverges
  | trap
  | otherReturn (value : Starlark.Value)
  | starlarkError (error : Starlark.RuntimeError)
  deriving DecidableEq, Repr

def observePython : Outcome Languages.Python.Core.Completion → Observation
  | .returned (.ok value) => .returned value
  | .returned (.error .zeroDivisionError) => .zeroDivision
  | .trap => .trap

def observeStarlark : Except Starlark.Failure Starlark.Value → Observation
  | .ok (.int value) => .returned value
  | .ok value => .otherReturn value
  | .error (.static _) => .rejected
  | .error (.dynamic (.zeroDivisor .floorDiv)) => .zeroDivision
  | .error (.dynamic error) => .starlarkError error

/-- Initial rejection, reachable policy UB and actual infinite traces retain
their own cases alongside finite operational outcomes. -/
inductive PythonObserves (profile : Languages.Python.Core.Profile) (body : Languages.Python.Core.Body) :
    Observation → Prop where
  | finite {outcome : Outcome Languages.Python.Core.Completion} :
      (Languages.Python.Core.model profile).May body outcome → PythonObserves profile body (observePython outcome)
  | rejected :
      (Languages.Python.Core.model profile).NoEntry body → PythonObserves profile body .rejected
  | unsupported :
      (Languages.Python.Core.model profile).UBReachable body → PythonObserves profile body .unsupported
  | diverges {start : Languages.Python.Core.State} :
      (Languages.Python.Core.model profile).initial body start →
      (Languages.Python.Core.semantics profile).toOpSem.Diverges start →
      PythonObserves profile body .diverges

def observeStarlarkExec : Starlark.Result Starlark.Completion → Observation
  | .ok result => observeStarlark (.ok (result.returned.getD .none))
  | .error error => observeStarlark (.error (.dynamic error))

/-- Empty globals and parameters. Resolution precedes relational execution. -/
inductive StarlarkObserves (body : Starlark.SourceStmt) : Observation → Prop where
  | rejected {error : Starlark.StaticError} :
      Starlark.resolveFunctionBody [] [] body = .error error → StarlarkObserves body .rejected
  | executes {stmt : Starlark.ResolvedStmt} {result : Starlark.Result Starlark.Completion} :
      Starlark.resolveFunctionBody [] [] body = .ok stmt →
      Starlark.Exec {} stmt result →
      StarlarkObserves body (observeStarlarkExec result)

/-- Equality of the projected operational observation predicates. -/
def Agree (body : IntBody) : Prop :=
  ∀ observation, PythonObserves .arithmetic body.python observation ↔ StarlarkObserves body.starlark observation

end Silmaril.Languages.PythonStarlark.ClosedReturn
