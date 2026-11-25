module

import Silmaril.Courses.Cambridge.L1.Concrete
import Silmaril.Courses.Cambridge.L2.Concrete
meta import Silmaril.Courses.Cambridge.L1.Concrete
meta import Silmaril.Courses.Cambridge.L2.Concrete

/-! Concrete byte regressions, built by the library's Courses glob. -/

namespace Silmaril.Courses.Cambridge.Concrete

#guard L1.Concrete.parse "(l0 := 3); !l0".toUTF8 =
    some (.seq (.assign "l0" (.int 3)) (.deref "l0"))

#guard L1.Concrete.parse "while (!l0>=0) do (l0:=(!l0+-1)) done".toUTF8 =
    some (.loop (.binary (.deref "l0") .ge (.int 0))
      (.assign "l0" (.binary (.deref "l0") .add (.int (-1)))))

#guard L1.Concrete.parse "if\ttrue\r\nthen 7 else −4".toUTF8 =
    some (.cond (.bool true) (.int 7) (.int (-4)))

#guard L1.Concrete.parseType "(unit)".toUTF8 = some .unit
#guard L1.Concrete.parse "1 + 2".toUTF8 = some (.binary (.int 1) .add (.int 2))
#guard L1.Concrete.parse "-123456789012345678901234567890".toUTF8 =
  some (.int (-123456789012345678901234567890))

private def counter : L1.Concrete.SourceExpr :=
  ⟨.seq (.assign "l0" (.int 3)) (.deref "l0"), by
    change (IsLocation "l0" ∧ True) ∧ IsLocation "l0"
    decide⟩

#guard String.fromUTF8? (L1.Concrete.print counter) =
    some "( ( l0 := 3 ) ; ! l0 )"

#guard L1.Concrete.parse (L1.Concrete.print counter) = some counter.val

#guard L2.Concrete.parse "((fun x:int->x) -19)".toUTF8 =
    some (.app (.lam "x" .int (.var "x")) (.int (-19)))

#guard L2.Concrete.parseResolved "fun x:int→(fun x:int→(x+y))".toUTF8 =
    some (.lam .int (.lam .int (.binary (.bvar 0) .add (.fvar "y"))))

#guard L2.Concrete.parseResolved "let x:int=x in x".toUTF8 =
    some (.letE .int (.fvar "x") (.bvar 0))

#guard L2.Concrete.parseResolved "let rec f:int→int=(fun x:int→(f x)) in (f 0)".toUTF8 =
    some (.letRecFun .int .int (.app (.bvar 1) (.bvar 0)) (.app (.bvar 0) (.int 0)))

#guard L2.Concrete.parseType "(int → bool) -> (unit -> int)".toUTF8 =
    some (.arr (.arr .int .bool) (.arr .unit .int))

#guard L2.Concrete.parseType (L2.Concrete.printType (.arr .int (.arr .bool .unit))) =
    some (.arr .int (.arr .bool .unit))

#guard L2.Concrete.parse "trueValue".toUTF8 = some (.var "trueValue")
#guard L2.Concrete.parse "fun lvalue:int→lvalue".toUTF8 =
    some (.lam "lvalue" .int (.var "lvalue"))
#guard L2.Concrete.parse "fun _id':bool→_id'".toUTF8 =
    some (.lam "_id'" .bool (.var "_id'"))

private def shadowing : L2.Concrete.SourceExpr :=
  ⟨.lam "x" .int (.lam "x" .int (.var "x")), by
    change IsVariable "x" ∧ IsVariable "x" ∧ IsVariable "x"
    decide⟩

#guard L2.Concrete.parse (L2.Concrete.print shadowing) = some shadowing.val
#guard L2.Concrete.parseResolved (L2.Concrete.print shadowing) =
    some (.lam .int (.lam .int (.bvar 0)))

-- Invalid UTF-8 cannot be either discarded or replaced by a valid token.
#guard L1.Concrete.parse (ByteArray.mk #[0x31, 0xc0, 0xaf]) = none
#guard L2.Concrete.parse (ByteArray.mk #[0xe2, 0x86]) = none

#guard L1.Concrete.parse "".toUTF8 = none
#guard L1.Concrete.parse "(1 + 2) )".toUTF8 = none
#guard L1.Concrete.parse "while true do skip".toUTF8 = none
#guard L1.Concrete.parse "(!l0 + (fun x:int→x))".toUTF8 = none
#guard L1.Concrete.parse "l0".toUTF8 = none
#guard L1.Concrete.parse "iftrue then 1 else 2".toUTF8 = none
#guard L1.Concrete.parse "123x".toUTF8 = none
#guard L1.Concrete.parseType "int -> int".toUTF8 = none
example : ¬ L1.Concrete.NamesOk (.deref "cell") := by
  change ¬ IsLocation "cell"
  decide

#guard L2.Concrete.parse "fun if:int→skip".toUTF8 = none
#guard L2.Concrete.parse "fun l0:int→skip".toUTF8 = none
#guard L2.Concrete.parse "fun x:int→x + 1".toUTF8 = none
#guard L2.Concrete.parse "let rec f:int→int=(fun x:bool→0) in (f 0)".toUTF8 =
    none
#guard L2.Concrete.parse "let x:int=1 x".toUTF8 = none
#guard L2.Concrete.parse "skip true false".toUTF8 = none
#guard L2.Concrete.parse "#0".toUTF8 = none
#guard L2.Concrete.parse "!x".toUTF8 = none
#guard L2.Concrete.parse "1_000".toUTF8 = none
#guard L2.Concrete.parse "λx:int→x".toUTF8 = none

end Silmaril.Courses.Cambridge.Concrete
