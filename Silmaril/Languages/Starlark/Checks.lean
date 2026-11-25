module

import Silmaril.Languages.Starlark.Thms
import all Silmaril.Languages.Starlark.Resolve.Defs

namespace Silmaril.Languages.Starlark

deriving instance DecidableEq for Except

private def readGlobal (body : SourceStmt) (name : String) : Except Failure (Option Value) :=
  (runModule body).map (fun globals => globals name)

private def divideByZero : SourceExpr := .binary .floorDiv (.int 1) (.int 0)

-- Arbitrary precision and floor semantics for either sign of divisor.
example :
    readGlobal (.assign "out" (.binary .mul (.int 111111111111111111111)
      (.int 111111111111111111111))) "out" = .ok (some (.int 12345679012345679012320987654320987654321)) :=
  by decide +kernel

example :
    readGlobal (.assign "out" (.binary .floorDiv (.int 7) (.int (-3)))) "out" =
      .ok (some (.int (-3))) ∧
    readGlobal (.assign "out" (.binary .mod (.int 7) (.int (-3)))) "out" =
      .ok (some (.int (-2))) ∧
    readGlobal (.assign "out" (.binary .mod (.int (-7)) (.int 3))) "out" =
      .ok (some (.int 2)) :=
  by decide +kernel

-- Booleans are a distinct type. Python gives True for the first expression.
example :
    readGlobal (.assign "out" (.binary .eq (.int 1) (.read "True"))) "out" =
      .ok (some (.bool false)) ∧
    readGlobal (.assign "out" (.binary .lt (.read "False") (.read "True"))) "out" =
      .ok (some (.bool true)) ∧
    readGlobal (.assign "out" (.binary .add (.int 1) (.read "True"))) "out" =
      .error (.dynamic (.binaryType .add)) :=
  by decide +kernel

-- Boolean operators preserve the selected operand and both forms of conditional are lazy.
example :
    readGlobal (.assign "out" (.logical .or (.int 3) divideByZero)) "out" =
      .ok (some (.int 3)) ∧
    readGlobal (.assign "out" (.logical .and (.int 0) divideByZero)) "out" =
      .ok (some (.int 0)) ∧
    readGlobal (.assign "out" (.conditional (.read "None") divideByZero (.int 4))) "out" =
      .ok (some (.int 4)) :=
  by decide +kernel

-- Local reassignment precedes early return, which skips the division.
example :
    runFunctionBody [("x", .int 9)] [("flag", .bool true)]
      (.seq (.assign "x" (.int 1))
        (.seq (.branch (.read "flag") (.assign "x" (.binary .add (.read "x") (.int 1))) .pass)
          (.seq (.ret (some (.read "x"))) (.eval divideByZero)))) = .ok (.int 2) :=
  by decide +kernel

example :
    runFunctionBody [] [] (.seq (.ret none) (.eval divideByZero)) = .ok .none ∧
    runFunctionBody [] [] .pass = .ok .none :=
  by decide +kernel

-- Scope is fixed before evaluation, so a skipped local assignment shadows the global.
example :
    runFunctionBody [("x", .int 9)] []
      (.seq (.branch (.read "False") (.assign "x" (.int 2)) .pass)
        (.ret (some (.read "x")))) =
      .error (.dynamic (.uninitialized ⟨.local, "x"⟩)) :=
  by decide +kernel

-- Module predeclared names are shadowable. A forward reference has a slot but no value yet.
example :
    readGlobal (.seq (.assign "True" (.int 9)) (.assign "out" (.read "True"))) "out" =
      .ok (some (.int 9)) ∧
    readGlobal (.seq (.assign "out" (.read "x")) (.assign "x" (.int 9))) "out" =
      .error (.dynamic (.uninitialized ⟨.global, "x"⟩)) :=
  by decide +kernel

-- Static checking visits dead code and precedes dynamic errors.
example :
    runFunctionBody [] []
      (.branch (.read "False") (.ret (some (.read "missing"))) (.ret (some (.int 3)))) =
        .error (.static (.undefinedName "missing")) ∧
    readGlobal (.seq (.assign "out" divideByZero) (.assign "out" (.int 1))) "out" =
      .error (.static (.duplicateGlobal "out")) ∧
    readGlobal (.branch (.read "True") .pass .pass) "out" = .error (.static .topLevelIf) :=
  by decide +kernel

-- The leftmost error wins. A primitive type error is checked after evaluating both operands.
example :
    readGlobal (.seq (.assign "out" (.binary .add (.read "x") divideByZero))
      (.assign "x" (.int 9))) "out" = .error (.dynamic (.uninitialized ⟨.global, "x"⟩)) ∧
    readGlobal (.assign "out" (.binary .add (.read "True") divideByZero)) "out" =
      .error (.dynamic (.zeroDivisor .floorDiv)) ∧
    readGlobal (.assign "out" (.binary .mod (.int 7) (.int 0))) "out" =
      .error (.dynamic (.zeroDivisor .mod)) :=
  by decide +kernel

end Silmaril.Languages.Starlark
