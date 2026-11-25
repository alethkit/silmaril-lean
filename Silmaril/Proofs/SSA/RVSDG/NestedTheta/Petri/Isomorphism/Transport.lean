module

public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Local

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs

open RVSDG.Isomorphism.Proofs (colours source_before site_length extend_length)
open NestedTheta.Isomorphism.Proofs (Slots store store_length compare_reads compare_completed completed)
open RVSDG.Petri (Tokens)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {argsL argsR outsL outsR : Ports (PortType V S)}
variable {sigsL sigsR : List (Ports (PortType V S))}
variable {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}

theorem renumbering_nonempty (iso : Graph.Isomorphic Op left right) : Nonempty (Renumbering Op left right) := by
  classical
  induction iso with
  | intro entry exit ids labels inputs results _ children =>
    exact ⟨.intro entry exit ids labels inputs results (fun i arm => Classical.choice (children i arm))⟩

theorem numbering_isomorphic (numbering : Renumbering Op left right) : Graph.Isomorphic Op left right := by
  induction numbering with
  | intro entry exit ids labels inputs results _ children =>
    exact .intro entry exit ids labels inputs results children

theorem laws (m : Model.{u, v, w} Op) (numbering : Renumbering Op left right) :
    Laws m left.toTerm right.toTerm (numbering.Matches m) := by
  induction numbering with
  | @intro argsL argsR outsL outsR sigsL sigsR left right entryEq exitEq ids labels inputs results children ih =>
    cases left with
    | region nodesL graphChildrenL resultsL =>
      cases right with
      | region nodesR graphChildrenR resultsR =>
        let graphL : Graph Op argsL [] sigsL outsL := .region nodesL graphChildrenL resultsL
        let graphR : Graph Op argsR [] sigsR outsR := .region nodesR graphChildrenR resultsR
        let tableL : Table Op argsL [] sigsL outsL :=
          ⟨nodesL, fun i arm => (graphChildrenL i arm).toTerm, resultsL⟩
        let tableR : Table Op argsR [] sigsR outsR :=
          ⟨nodesR, fun i arm => (graphChildrenR i arm).toTerm, resultsR⟩
        let numbering : Renumbering Op graphL graphR :=
          .intro entryEq exitEq ids labels inputs results children
        change Laws m tableL.term tableR.term (numbering.Matches m)
        let empty : Slots m.Val [] := PUnit.unit
        have published_eq {markL : Marking m tableL.term} {markR : Marking m tableR.term}
            (paired : numbering.Matches m markL markR) (i : Nat) (valid : i < sigsL.length) :
            (store (tableL.outputs m markL empty))[i]? =
              (store (tableR.outputs m markR empty))[renameVertex ids i]? := by
          let j : Fin sigsL.length := ⟨i, valid⟩
          have atL := tableL.output_at m markL empty j
          have atR := tableR.output_at m markR empty (ids j)
          simp only [List.length_nil, Nat.zero_add] at atL atR
          simp only [renameVertex, dite_eq_left valid]
          change (store (tableL.outputs m markL empty))[j.val]? =
            (store (tableR.outputs m markR empty))[(ids j).val]?
          rw [atL, atR]
          exact congrArg some (published_matched m (labels j) (paired j))
        have read_eq {entryL : Tuple m.Val argsL} {entryR : Tuple m.Val argsR}
            (sameEntry : colours entryL = colours entryR)
            {markL : Marking m tableL.term} {markR : Marking m tableR.term}
            (paired : numbering.Matches m markL markR) (i : Fin sigsL.length) :
            (tableL.readAt m entryL empty markL i).map colours =
              (tableR.readAt m entryR empty markR (ids i)).map colours := by
          unfold Table.readAt
          rw [read_slots, read_slots]
          refine compare_reads _ _ entryL entryR sameEntry _ _
            (tableL.prefix_outputs m markL empty i)
            (tableR.prefix_outputs m markR empty (ids i))
            (renameVertex ids) (inputs i) ?_
          intro producer port present
          have h : producer < i.val := by
            simpa only [site_length, List.length_nil, Nat.zero_add] using
              source_before (nodesL i).inputs present
          exact published_eq paired producer (Nat.lt_trans h i.isLt)
        have update {markL : Marking m tableL.term} {markR : Marking m tableR.term}
            (paired : numbering.Matches m markL markR) (i : Fin sigsL.length)
            (nextL : tableL.cell m i) (nextR : tableR.cell m (ids i))
            (changed : Local.Matches m (labels i) (fun arm => (children i arm).Matches m) nextL nextR) :
            numbering.Matches m (tableL.set m markL i nextL) (tableR.set m markR (ids i) nextR) := by
          intro j
          change Local.Matches m (labels j) (fun arm => (children j arm).Matches m)
            (tableL.get m (tableL.set m markL i nextL) j)
            (tableR.get m (tableR.set m markR (ids i) nextR) (ids j))
          by_cases same : j = i
          · subst j
            rw [tableL.get_set_self, tableR.get_set_self]
            exact changed
          · rw [tableL.get_set_other m markL i j nextL same,
              tableR.get_set_other m markR (ids i) (ids j) nextR (fun eq => same (ids.injective eq))]
            exact paired j
        have cell_markings (i : Fin sigsL.length) :=
          local_markings m (labels i) (C := fun j => Marking m (tableL.children i j))
            (D := fun j => Marking m (tableR.children (ids i) j))
            (rel := fun arm => (children i arm).Matches m)
            (fun arm => (ih i arm).unique_right) (fun arm => (ih i arm).unique_left)
        constructor
        · intro i
          change Local.Matches m (labels i) (fun arm => (children i arm).Matches m)
            (tableL.get m (pending m tableL.term) i) (tableR.get m (pending m tableR.term) (ids i))
          rw [tableL.get_pending, tableR.get_pending]
          exact pending_pair m (labels i) (C := fun j => Marking m (tableL.children i j))
            (D := fun j => Marking m (tableR.children (ids i) j)) (fun arm => (children i arm).Matches m)
        · intro markL
          let property (j : Fin sigsR.length) (cell : tableR.cell m j) : Prop :=
            ∀ (i : Fin sigsL.length) (atImage : ids i = j),
              Local.Matches m (labels i) (fun arm => (children i arm).Matches m)
                (tableL.get m markL i) (atImage.symm ▸ cell)
          have selected (j : Fin sigsR.length) : ∃! cell, property j cell := by
            obtain ⟨i, rfl⟩ := ids.surjective j
            refine (existsUnique_congr (fun cell => ?_)).2 ((cell_markings i).1 (tableL.get m markL i))
            constructor
            · intro built
              exact built i rfl
            · intro related k eq
              have same := ids.injective eq
              subst k
              exact related
          apply (existsUnique_congr (fun markR => ?_)).1 (tableR.unique_of_cells m property selected)
          constructor
          · intro built i
            exact built (ids i) i rfl
          · intro paired j i eq
            subst j
            exact paired i
        · intro markR
          exact tableL.unique_of_cells m
            (fun i cell => Local.Matches m (labels i) (fun arm => (children i arm).Matches m)
              cell (tableR.get m markR (ids i)))
            (fun i => (cell_markings i).2 (tableR.get m markR (ids i)))
        · intro entryL entryR sameEntry markL markR paired
          let slotsL := tableL.outputs m markL empty
          let slotsR := tableR.outputs m markR empty
          have lenL : (store slotsL).length = sigsL.length := by simp [store_length, extend_length]
          have lenR : (store slotsR).length = sigsR.length := by simp [store_length, extend_length]
          have done := compare_completed ids (store slotsL) (store slotsR) lenL lenR (published_eq paired)
          have finishL := tableL.finished_outputs m entryL empty markL (by rfl)
          have finishR := tableR.finished_outputs m entryR empty markR (by rfl)
          change (finished m tableL.term entryL (tokens empty) markL).map colours =
            (finished m tableR.term entryR (tokens empty) markR).map colours
          rw [finishL, finishR]
          change (if completed (store slotsL) then
            NestedTheta.Isomorphism.Proofs.read tableL.results entryL slotsL else none).map colours =
            (if completed (store slotsR) then
              NestedTheta.Isomorphism.Proofs.read tableR.results entryR slotsR else none).map colours
          by_cases status : completed (store slotsL)
          · have statusR : completed (store slotsR) := Eq.mp done status
            simp only [ite_eq_left status, ite_eq_left statusR]
            refine compare_reads _ _ entryL entryR sameEntry _ _
              ⟨[], List.append_nil _⟩ ⟨[], List.append_nil _⟩ (renameVertex ids) results ?_
            intro producer port present
            apply published_eq paired
            simpa only [extend_length, List.length_nil, Nat.zero_add] using
              source_before resultsL present
          · have statusR : ¬ completed (store slotsR) := fun h => status (Eq.mpr done h)
            simp only [ite_eq_right status, ite_eq_right statusR, Option.map_none]
        · intro entryL entryR sameEntry markL newL markR paired step
          obtain ⟨i, cellL, atL, rfl⟩ := tableL.localize m entryL empty markL newL step
          obtain ⟨cellR, atR, related⟩ := (local_steps m (labels i)
            (tableL.children i) (tableR.children (ids i)) (ih i) (read_eq sameEntry paired i)
            (paired i)).1 cellL atL
          exact ⟨_, tableR.fire_set m entryR empty markR (ids i) cellR atR,
            update paired i cellL cellR related⟩
        · intro entryL entryR sameEntry markL markR newR paired step
          obtain ⟨j, cellR, atR, rfl⟩ := tableR.localize m entryR empty markR newR step
          let i := ids.symm j
          have mapped : ids i = j := ids.apply_symm_apply j
          clear step
          revert cellR atR
          rw [← mapped]
          intro cellR atR
          obtain ⟨cellL, atL, related⟩ := (local_steps m (labels i)
            (tableL.children i) (tableR.children (ids i)) (ih i) (read_eq sameEntry paired i)
            (paired i)).2 cellR atR
          exact ⟨_, tableL.fire_set m entryL empty markL i cellL atL, update paired i cellL cellR related⟩

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs
