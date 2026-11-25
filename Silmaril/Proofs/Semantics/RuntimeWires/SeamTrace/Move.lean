module

public import Silmaril.Proofs.Semantics.RuntimeWires.SeamTrace.Context
import Silmaril.Semantics.RuntimeWires.ProgressiveTrace.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.SeamTrace

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

private theorem splitRoute_match (row : ℕ) (destinations : List BoxAddress) :
    RoutesBoxes (splitRoute row destinations) row 0 destinations := by
  intro i hi
  simp [splitRoute, List.getElem?_eq_getElem hi]

private theorem trace_split {A M B C : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B}
    (split : Row.Split S r p q) (tail : Sheet S B C) (row : ℕ) :
    ∃ destinations : List BoxAddress,
      ∀ input : List (NamedWire O), input.length = A.length →
        let route := splitRoute row destinations
        ((Sheet.cons r tail).traceWiresFrom row input).RenamedAt
          ((Sheet.cons p (.cons q tail)).traceWiresFrom row (input.map (NamedWire.rename route)))
          route row row := by
  obtain ⟨destinations, _, localTrace⟩ := trace_split_rows split row 0 0
  refine ⟨destinations, ?_⟩
  intro input length
  let route := splitRoute row destinations
  have front := localTrace route 0 (splitRoute_match row destinations) input length
  have suffix := trace_suffix_rename tail route (row + 1) (row + 1 + 1)
    (fun n k => by
      have above : row < row + 1 + n := by omega
      simp [route, splitRoute, not_lt_of_ge above.le, ne_of_gt above]
      omega) (r.traceWires row 0 input).frontier
  have ports := front.1
  simp only [traceSplitRows] at ports
  rw [ports] at suffix
  constructor
  · have boxes := front.2.append suffix.occurrences
    simpa only [Sheet.traceWiresFrom, addressRows, List.map_append, traceSplitRows, List.append_assoc]
      using boxes
  · exact suffix.outputs

/-- An elementary move gives the named incidence correspondence inside
any common prefix and continuation. -/
theorem trace_move {A B : List O} {p q : Sheet S A B} (move : Sheet.Move S p q) (row : ℕ) :
    ∃ route : BoxAddress → BoxAddress,
      (∀ loc : BoxAddress, loc.1 < row → route loc = loc) ∧
      ∀ input : List (NamedWire O), input.length = A.length →
        (p.traceWiresFrom row input).RenamedAt
          (q.traceWiresFrom row (input.map (NamedWire.rename route))) route row row := by
  induction move generalizing row with
  | split split tail =>
    obtain ⟨dest, trace⟩ := trace_split split tail row
    exact ⟨splitRoute row dest, fun loc earlier => by simp [splitRoute, earlier], trace⟩
  | straight tail =>
    let route : BoxAddress → BoxAddress := fun loc =>
      if loc.1 < row then loc else (loc.1 + 1, loc.2)
    refine ⟨route, fun loc earlier => by simp [route, earlier], ?_⟩
    intro input count
    have suffix := trace_suffix_rename tail route row (row + 1) (fun n k => by
      change (if row + n < row then (row + n, k) else (row + n + 1, k)) = (row + 1 + n, k)
      rw [ite_eq_right (by omega)]
      exact Prod.ext (by omega) rfl) input
    have straight := Row.traceWires_straight (S := S) _ (input.map (NamedWire.rename route))
      (by simpa using count) row 0
    constructor
    · simpa only [Sheet.traceWiresFrom, straight, addressRows, addressBoxes, List.nil_append]
        using suffix.occurrences
    · simpa only [Sheet.traceWiresFrom, straight] using suffix.outputs
  | under r move ih =>
    obtain ⟨route, earlier, trace⟩ := ih (row + 1)
    refine ⟨route, fun loc h => earlier loc (h.trans (Nat.lt_succ_self _)), ?_⟩
    intro input count
    have head := trace_row_rename r route row row 0 (fun k => earlier (row, k) (Nat.lt_succ_self _)) input
    have rest := trace _ (output_length r row 0 input count)
    rw [head.1] at rest
    constructor
    · simp only [Sheet.traceWiresFrom, addressRows, List.map_append, head.2]
      exact rest.occurrences.append_left _
    · exact rest.outputs

theorem trace_move_bare {A B : List O} {p q : Sheet S A B} (move : Sheet.Move S p q) :
    ∃ route, p.traceWires.Renamed q.traceWires route := by
  obtain ⟨route, _, trace⟩ := trace_move move 0
  have boundary : (namePorts .boundary A).map (NamedWire.rename route) = namePorts .boundary A := by
    simp [namePorts, List.map_map, Function.comp_def, NamedWire.rename, WireOrigin.rename]
  have h := trace (namePorts .boundary A) (by simp [namePorts])
  rw [boundary] at h
  exact ⟨route, h⟩

end Silmaril.RuntimeWires.Proofs.SeamTrace
