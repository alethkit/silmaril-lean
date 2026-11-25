module

public import Silmaril.Courses.Cambridge.L2.Syntax

/-! Lexical closure values shared by the environment semantics and interpreter. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2

inductive RuntimeValue where
  | int (value : Int)
  | bool (value : Bool)
  | unit
  | closure (domain : Ty) (body : Expr) (environment : List RuntimeValue)
  | recursive (domain codomain : Ty) (body : Expr)
      (environment : List RuntimeValue)
  deriving Repr

abbrev RuntimeEnv := List RuntimeValue

/-- Observe ground results in the same configuration shape as the small-step interpreter. -/
def RuntimeValue.groundExpr : RuntimeValue → Option Expr
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .unit => some .skip
  | .closure _ _ _ | .recursive _ _ _ _ => none

end Silmaril.Courses.Cambridge.L2
