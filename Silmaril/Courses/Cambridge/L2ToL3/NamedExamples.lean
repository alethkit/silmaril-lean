module

import Silmaril.Courses.Cambridge.L2.Concrete
meta import Silmaril.Courses.Cambridge.L2.Concrete
import Silmaril.Courses.Cambridge.L2ToL3.Named

open Silmaril.Courses.Cambridge
open L2ToL3

-- An ambient binder shadows the variable only. The second, unmatched name is free.
example (address : Layout) :
    (named address (.assign "cell" (.binary (.var "cell") .add (.var "free")))).resolve
      ["outer", "cell", "cell"] =
    .assign (.loc (address "cell")) (.binary (.bvar 1) .add (.fvar "free")) := rfl

private def source : ByteArray := "let rec f:int→int=(fun x:int→(l:=x); !l) in f y".toUTF8

private def sourceTerm : L2.RawExpr :=
  .letRecFun "f" "x" .int .int (.seq (.assign "l" (.var "x")) (.deref "l"))
    (.app (.var "f") (.var "y"))

#guard L2.Concrete.parse source = some sourceTerm

private def targetTerm (address : Layout) : L3.Concrete.SourceExpr :=
  ⟨named address sourceTerm, by
    simp only [sourceTerm, named, ty, L3.Concrete.ExprNames, L3.Concrete.TypeNames,
      true_and, and_true]
    decide⟩

example (address : Layout) :
    L3.Concrete.parse (L3.Concrete.print (targetTerm address)) =
      some (.letRecFun "f" "x" .int .int
        (.seq (.assign (.loc (address "l")) (.var "x")) (.deref (.loc (address "l"))))
        (.app (.var "f") (.var "y"))) :=
  L3.Concrete.parse_print (targetTerm address)

example (address : Layout) :
    L3.Concrete.parseResolved (L3.Concrete.print (targetTerm address)) =
      some (.letRecFun .int .int
        (.seq (.assign (.loc (address "l")) (.bvar 0)) (.deref (.loc (address "l"))))
        (.app (.bvar 0) (.fvar "y"))) :=
  parseResolved_print_named address sourceTerm (targetTerm address).property

-- L3 reserves `ref`, although L2 accepts it as a variable.
#guard L2.Concrete.parse "ref".toUTF8 = some (.var "ref")

example (address : Layout) : ¬ L3.Concrete.NamesOk (named address (.var "ref")) := by
  change ¬ L3.Concrete.IsName "ref"
  decide
