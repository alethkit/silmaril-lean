module

import Silmaril.SSA.RVSDG.LambdaSSA.Region.Thms

namespace Silmaril.SSA.RVSDG.LambdaSSA.RegionTests

open Silmaril.Isotope.LambdaSSA (Tm Region)

private abbrev T := Silmaril.Ty Unit
private abbrev word : T := .base ()

private inductive Instr where
  | tick

private instance : HasTy Instr T where
  src _ := word
  trg _ := word

private def sequential : Region Instr :=
  .let₁ (.op Instr.tick (.var 0)) (.br 0 (.var 0))

private def sequentialForm : RegionForm sequential [word] word :=
  ⟨.let₁ (.op Instr.tick (.var 0)) (.var 0),
    .let₁ _ (.exit _), .bind Instr.tick .head (.ret .head)⟩

example : Region.HasType [word] sequential [word] :=
  (lowerRegion sequentialForm).2.2.typing

private abbrev payload : List T := [word, word, word]
private def pick : Fin 3 → Port payload word :=
  Fin.cases (.tail (.tail .head)) (Fin.cases .head (fun _ => .tail .head))

private def caseRegion : Region Instr :=
  .case (.var 0) (.br 0 (.var 4)) (.case (.var 0) (.br 0 (.var 3)) (.br 0 (.var 4)))

private def expression : Tm Instr :=
  .case (.var 0) (.var 4) (.case (.var 0) (.var 3) (.var 4))

private def scopedForm : GammaRegionForm caseRegion 1 payload word :=
  ⟨expression, (exitExpression_eq_some).mp rfl, ⟨pick, rfl⟩⟩

example : Region.HasType (selectorType 2 :: payload) caseRegion [word] :=
  (lowerGammaRegion scopedForm).2.typing

private def graph : GammaGraph Instr 1 payload word := (lowerGammaRegion scopedForm).1

private def graphForm : GammaRVForm 1 graph.toTerm := by
  refine ⟨pick, ?_⟩
  change gammaTerm (Φ := Instr) 1 pick = (gammaTerm 1 pick).toGraph.toTerm
  exact (Term.toTerm_toGraph _).symm

example : (raiseGammaRegion graph graphForm).1 = caseRegion := rfl

example : Region.HasType (selectorType 2 :: payload) (raiseGammaRegion graph graphForm).1 [word] :=
  (raiseGammaRegion graph graphForm).2.typing

example : exitExpression (.br 1 (.var 0) : Region Instr) = none := rfl

example : exitExpression (.cfg (.br 0 (.var 0)) 0 (fun i => i.elim0) : Region Instr) = none := rfl

end Silmaril.SSA.RVSDG.LambdaSSA.RegionTests
