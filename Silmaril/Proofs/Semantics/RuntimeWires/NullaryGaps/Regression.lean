module

public import Silmaril.Semantics.RuntimeWires.NullaryGaps.Thms
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.RuntimeWires.Proofs.NullaryGaps.Regression

open Silmaril.RuntimeWires.Sliced

private abbrev signature : Signature Unit where
  Edge := Bool
  source _ := []
  target _ := []

private theorem nullary (e : signature.Edge) : signature.source e = [] ∧ signature.target e = [] :=
  ⟨rfl, rfl⟩

private def boxes {A B : List Unit} (labels : List Bool) (tail : Row signature A B) :
    Row signature A B :=
  match labels with
  | [] => tail
  | e :: rest => Row.box (S := signature) e (boxes rest tail)

private def row (left middle right : List Bool) : Row signature [(), ()] [(), ()] :=
  boxes left (.wire () (boxes middle (.wire () (boxes right .empty))))

private def twoRows : Sheet signature [(), ()] [(), ()] :=
  .cons (row [true, false] [true] [false]) (.cons (row [true] [false] []) (.empty _))

private def rescheduled : Sheet signature [(), ()] [(), ()] :=
  .cons (row [true, true, false] [false, true] [false]) (.empty _)

private def movedAcross : Sheet signature [(), ()] [(), ()] :=
  .cons (row [true, true, false, false] [false, true] []) (.empty _)

example : twoRows.boxCount = movedAcross.boxCount := rfl

/-- Consolidate across rows and permute within gaps, preserving the two
copies of the repeated label. -/
example : Sheet.SeamEquivalent twoRows rescheduled := by
  apply (Sheet.seamEquivalent_iff_gapMultisets_eq nullary).mpr
  funext i
  change Fin 3 at i
  fin_cases i
  · exact Multiset.coe_eq_coe.mpr ((List.Perm.swap true false []).cons true)
  · exact Multiset.coe_eq_coe.mpr (List.Perm.swap false true [])
  · rfl

/-- The same boxes cannot all be placed in different gaps. -/
example : ¬ Sheet.SeamEquivalent twoRows movedAcross := by
  intro same
  have gap : ([false] : Multiset Bool) = ([] : List Bool) :=
    congrFun ((Sheet.seamEquivalent_iff_gapMultisets_eq nullary).mp same) ⟨2, by decide⟩
  have impossible := (Multiset.coe_eq_coe.mp gap).length_eq
  cases impossible

private def unwired (labels : List Bool) : Sheet signature [] [] :=
  .cons (boxes labels .empty) (.empty _)

example : Sheet.SeamEquivalent (unwired [true, false, true]) (unwired [true, true, false]) := by
  apply (Sheet.seamEquivalent_iff_gapMultisets_eq nullary).mpr
  funext i
  change Fin 1 at i
  fin_cases i
  exact Multiset.coe_eq_coe.mpr ((List.Perm.swap true false []).cons true)

end Silmaril.RuntimeWires.Proofs.NullaryGaps.Regression
