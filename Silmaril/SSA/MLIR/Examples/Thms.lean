module

import Silmaril.SSA.MLIR.Thms

/-! Smoke checks using only the public MLIR facade. -/

namespace Silmaril.MLIR.Examples

open Silmaril.MLIR.Arith
open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.Morphism

private def i1 : Width := ⟨1, by decide⟩
private def i8 : Width := ⟨8, by decide⟩

private def plain : Block [] i8 :=
  .letOp (.constant 255#8)
    (.letOp (.binary .addi .here .here) (.yield .here))

private def plainInput : Env [] := .nil

-- The inner region changes width from i8 to i1. The enclosing block
-- explicitly passes the older input, then adds the original i1 input.
private def nested : Block [i1, i8] i1 :=
  .letRegion (.there .here)
    (.letRegion .here (.letOp (.constant 1#1) (.yield .here)) (.yield .here))
    (.letOp (.binary .addi .here (.there .here)) (.yield .here))

private def nestedInput : Env [i1, i8] := .cons 1#1 (.cons 42#8 .nil)

example : Silmaril.Isotope.LambdaSSA.Region.HasType
    [Ty.base i1, .base i8] nested.toLambdaSSA [.base i1] :=
  nested.toLambdaSSA_hasType

example : Silmaril.Isotope.LetIter.LocallyNameless.HasType Prim .nil
    (.snoc (.snoc .nil (Ty.base i8)) (.base i1)) nested.toLetIter (.base i1) :=
  nested.toLetIter_hasType

example : ssaBeh 1 plainInput.observationModel plain.toScopedLambdaSSA =
    {Observation.ret () (0, word (w := i8) 254#8) ()} :=
  plain.toLambdaSSA_observations plainInput

example : iterBeh plainInput.observationModel plain.toLetIter =
    {Observation.ret () (word (w := i8) 254#8) ()} :=
  plain.toLetIter_observations plainInput

example : ssaBeh 1 nestedInput.observationModel nested.toScopedLambdaSSA =
    {Observation.ret () (0, word (w := i1) 0#1) ()} :=
  nested.toLambdaSSA_observations nestedInput

example : iterBeh nestedInput.observationModel nested.toLetIter =
    {Observation.ret () (word (w := i1) 0#1) ()} :=
  nested.toLetIter_observations nestedInput

example : SSAIter.quotEquiv (Quotient.mk (SSAIter.regionSetoid.{0, 0, 0} Prim 1 2)
    nested.toScopedLambdaSSA) =
    Quotient.mk (SSAIter.termSetoid.{0, 0, 0} Prim 2) nested.toLetIter :=
  nested.toLetIter_quotEquiv

end Silmaril.MLIR.Examples
