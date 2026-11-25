module

public import Silmaril.Proofs.Semantics.RuntimeWires.SeamTrace.Rows

public section

namespace Silmaril.RuntimeWires.Proofs.SeamTrace

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

theorem output_length {A B : List O} (r : Row S A B) (row box : ℕ)
    (input : List (NamedWire O)) (size : input.length = A.length) :
    (r.traceWires row box input).frontier.length = B.length := by
  induction r generalizing box input with
  | empty => rfl
  | wire x r ih =>
    cases input with
    | nil => simp at size
    | cons w input =>
      have tail := ih box input (Nat.succ.inj size)
      simp [Row.traceWires, tail]
  | box e r ih =>
    have tail := ih (box + 1) (input.drop (S.source e).length) (by simp [size])
    simp [Row.traceWires, namePorts, tail]

/-- A row at another height has the same port lists with the transported
source names. No restriction on those incoming names is needed. -/
theorem trace_row_rename {A B : List O} (r : Row S A B) (route : BoxAddress → BoxAddress)
    (row row' box : ℕ) (addresses : ∀ k, route (row, k) = (row', k))
    (input : List (NamedWire O)) :
    let before := r.traceWires row box input
    let after := r.traceWires row' box (input.map (NamedWire.rename route))
    before.frontier.map (NamedWire.rename route) = after.frontier ∧
      (addressBoxes row box before.boxes).map (BoxOccurrence.rename route) =
        addressBoxes row' box after.boxes := by
  induction r generalizing box input with
  | empty => exact ⟨rfl, rfl⟩
  | wire x r ih =>
    have tail := ih box input.tail
    constructor
    · simpa [Row.traceWires, List.map_take, List.map_tail] using
        congrArg ((input.take 1).map (NamedWire.rename route) ++ ·) tail.1
    · simpa [Row.traceWires, List.map_tail] using tail.2
  | box e r ih =>
    have tail := ih (box + 1) (input.drop (S.source e).length)
    have names := rename_ports route row box (S.target e)
    rw [addresses] at names
    constructor
    · simpa [Row.traceWires, List.map_append, List.map_drop, names] using
        congrArg (namePorts (.box row' box) (S.target e) ++ ·) tail.1
    · have same := congrArg
        (List.cons ((row', box), ⟨e, (input.take (S.source e).length).map (NamedWire.rename route),
          namePorts (.box row' box) (S.target e)⟩)) tail.2
      simpa [Row.traceWires, addressBoxes, BoxOccurrence.rename, BoxTrace.rename, List.map_take,
        List.map_drop, addresses, names] using same

theorem trace_suffix_rename {A B : List O} (sheet : Sheet S A B) (route : BoxAddress → BoxAddress)
    (row row' : ℕ) (addresses : ∀ n k, route (row + n, k) = (row' + n, k))
    (input : List (NamedWire O)) :
    (sheet.traceWiresFrom row input).RenamedAt
      (sheet.traceWiresFrom row' (input.map (NamedWire.rename route))) route row row' := by
  induction sheet generalizing row row' input with
  | empty => exact ⟨.nil, rfl⟩
  | cons r rest ih =>
    have head := trace_row_rename r route row row' 0 (fun k => by simpa using addresses 0 k) input
    have tail := ih (row + 1) (row' + 1) (fun n k => by
      simpa only [Nat.add_assoc] using addresses (1 + n) k)
      (r.traceWires row 0 input).frontier
    rw [head.1] at tail
    constructor
    · simp only [Sheet.traceWiresFrom, addressRows, List.map_append, head.2]
      exact tail.occurrences.append_left _
    · exact tail.outputs

end Silmaril.RuntimeWires.Proofs.SeamTrace
