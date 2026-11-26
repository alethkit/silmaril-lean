module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Multiple.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Multiple.Signature.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Signature.Thms

/-! # Regression for a noninjective map and two reset values -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleExample

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing ResetTables.Multiple ResetTables.Multiple.Example
open UnitSumSquare.Cycles.Mixed.MergeCycle (result source target tags)
open ForwardingTables (inj obj)
open scoped Paper.BoundSimulation.Obstruction

set_option backward.isDefEq.respectTransparency false

theorem projected_square :
    projection.map (step P result source sourceSteps ≫
      coprod.map (𝟙 (obj P result)) (stateMap P source target stateRows)) =
    projection.map (stateMap P source target stateRows ≫ step P result target targetSteps) := by
  apply congrArg projection.map
  apply square_of_codes
  rintro ((i | i) | (i | i)) <;> cases i <;> rfl

theorem distinct_actions :
    projection.map (action (Φ := Empty) P (some left)) ≠ projection.map (action P (some right)) := by
  intro e
  have same := Option.some.inj (action_injective P e)
  have terms := congrArg Subtype.val same
  change (Tm.inl .unit : Tm Empty) = .inr .unit at terms
  cases terms

theorem not_mono : ¬ Mono (stateMap P source target stateRows) := by
  intro mono
  let x : source.Row := .inl (.inl ())
  let y : source.Row := .inl (.inr ())
  have eq : inj (Φ := Empty) P source x = inj P source y := by
    apply (cancel_mono (stateMap P source target stateRows)).mp
    rw [inj_stateMap, inj_stateMap]
    rfl
  have sep : ForwardingTables.SeparatesTags (Φ := Empty) P := by
    intro h
    have impossible := (ForwardingTables.not_separatesTags_iff (Φ := Empty) P).mp (fun distinct => distinct h)
    cases impossible with
    | sum h _ => cases h
  have outputs : projection.map (ForwardingTables.output (Φ := Empty) P source .empty (.inl x)) =
      projection.map (ForwardingTables.output (Φ := Empty) P source .empty (.inl y)) :=
    congrArg (fun f => projection.map (f ≫ coprod.inl)) eq
  have same := Sum.inl.inj (ForwardingTables.separate_output P sep source .empty outputs)
  change (Sum.inl (Sum.inl ()) : source.Row) = Sum.inl (Sum.inr ()) at same
  cases Sum.inl.inj same

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleExample
