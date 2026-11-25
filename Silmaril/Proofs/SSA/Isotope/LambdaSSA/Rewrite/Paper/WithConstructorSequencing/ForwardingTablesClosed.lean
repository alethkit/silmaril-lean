module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.Observation.Thms

/-! # Detecting forwarded tags on instruction-free payloads -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesClosed

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing ForwardingTables
open UnitSumSquare (Shape)
open UnitSumSquare.Cycles.Mixed.MergeCycle (result source target tags sourceRows targetRows)
open scoped Paper.BoundSimulation.Obstruction

set_option backward.isDefEq.respectTransparency false

theorem separates_of_closed {P : Ty Empty} {w : Tm Empty} (hw : Tm.BranchValue [] w P) :
    SeparatesTags (Φ := Empty) P := by
  intro eq
  rw [← sumCofan_inl_sumIso_hom P P, ← sumCofan_inr_sumIso_hom P P,
    projection.map_comp, projection.map_comp] at eq
  have h := (cancel_mono (projection.map (sumIso P P).hom)).mp eq
  rw [sumCofan_inl, sumCofan_inr] at h
  have typed := (Paper.Extension.Singleton.ofRegion_eq_iff Seed
    (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))
    (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))).mp h
  have observed := Paper.BoundSimulation.Obstruction.PairSequencing.branch_observation_of_closed_input
    (.inl (.var (i := 0) rfl)) (.inr (.var (i := 0) rfl)) hw typed
  cases observed

private theorem closed_or_empty (P : Ty Empty) :
    (∃ w : Tm Empty, Tm.BranchValue [] w P) ∨ Paper.StructurallyEmpty P := by
  induction P with
  | base a => exact a.elim
  | empty => exact .inr .empty
  | unit => exact .inl ⟨.unit, .unit⟩
  | coprod A B ihA ihB =>
    rcases ihA with ⟨a, ha⟩ | hA
    · exact .inl ⟨.inl a, .inl ha⟩
    · rcases ihB with ⟨b, hb⟩ | hB
      · exact .inl ⟨.inr b, .inr hb⟩
      · exact .inr (.sum hA hB)
  | product A B ihA ihB =>
    rcases ihA with ⟨a, ha⟩ | hA
    · rcases ihB with ⟨b, hb⟩ | hB
      · exact .inl ⟨.pair a b, .pair ha hb⟩
      · exact .inr (.right hB)
    · exact .inr (.left hA)

theorem initial_of_no_closed_value (P : Ty Empty) (h : ¬ ∃ w : Tm Empty, Tm.BranchValue [] w P) :
    Nonempty (IsInitial (ofType (Φ := Empty) P)) := by
  exact ((closed_or_empty P).resolve_left h).initial

theorem separates_or_initial (P : Ty Empty) :
    SeparatesTags (Φ := Empty) P ∨ Nonempty (IsInitial (ofType (Φ := Empty) P)) := by
  rcases closed_or_empty P with ⟨w, hw⟩ | hP
  · exact .inl (separates_of_closed hw)
  · exact .inr (hP.initial)

abbrev payload : Ty Empty := .product .unit (.coprod .unit .unit)

private theorem sample_separates : SeparatesTags (Φ := Empty) payload :=
  separates_of_closed (.pair .unit (.inl .unit))

theorem projected_square :
    projection.map (step (Φ := Empty) payload result source sourceRows ≫
      coprod.map (𝟙 (obj payload result)) (stateMap payload source target tags)) =
    projection.map (stateMap payload source target tags ≫ step payload result target targetRows) := by
  apply congrArg projection.map
  apply square_of_tags
  rintro ((i | i) | (i | i)) <;> cases i <;> rfl

theorem not_mono : ¬ Mono (stateMap (Φ := Empty) payload source target tags) := by
  intro mono
  let left : source.Row := .inl (.inl ())
  let right : source.Row := .inl (.inr ())
  have e : inj (Φ := Empty) payload source left = inj payload source right := by
    apply (cancel_mono (stateMap payload source target tags)).mp
    rw [stateMap, inj_table, inj_table]
    rfl
  have outputs : projection.map (output (Φ := Empty) payload source .empty (.inl left)) =
      projection.map (output (Φ := Empty) payload source .empty (.inl right)) :=
    congrArg (fun f => projection.map (f ≫ coprod.inl)) e
  have same := separate_output payload sample_separates source .empty outputs
  have tagsEqual := Sum.inl.inj same
  change (Sum.inl (Sum.inl ()) : source.Row) = Sum.inl (Sum.inr ()) at tagsEqual
  cases Sum.inl.inj tagsEqual

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesClosed
