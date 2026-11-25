module

public import Silmaril.Semantics.RuntimeWires.SeamTrace.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.SeamTrace.Regression

open Silmaril.RuntimeWires.Sliced

private inductive Edge
  | source
  | sink
  | scalar

private abbrev signature : Silmaril.RuntimeWires.Signature Unit where
  Edge := Edge
  source
    | Edge.sink => [()]
    | _ => []
  target
    | Edge.source => [()]
    | _ => []

-- Two wires cross the split. One is produced in the prefix and one
-- runs from the input cap to the final output cap.
private def prefixRow : Row signature [()] [(), ()] :=
  Row.box (S := signature) Edge.source (.wire () .empty)

private def joint : Row signature [(), ()] [(), (), ()] :=
  Row.box (S := signature) Edge.scalar (.wire () (Row.box (S := signature) Edge.source (.wire () .empty)))

private def upper : Row signature [(), ()] [(), (), ()] :=
  .wire () (Row.box (S := signature) Edge.source (.wire () .empty))

private def lower : Row signature [(), (), ()] [(), (), ()] :=
  Row.box (S := signature) Edge.scalar (.wire () (.wire () (.wire () .empty)))

private def suffix : Sheet signature [(), (), ()] [(), ()] :=
  .cons (Row.box (S := signature) Edge.sink
    (Row.box (S := signature) Edge.sink (Row.box (S := signature) Edge.source (.wire () .empty)))) (.empty _)

private theorem rowSplit : Row.Split signature joint upper lower :=
  Row.Split.lower (S := signature) Edge.scalar (.wire () (Row.Split.upper (S := signature) Edge.source (.wire () .empty)))

private def original : Sheet signature [()] [(), ()] := .cons prefixRow (.cons joint suffix)

private def sliced : Sheet signature [()] [(), ()] := .cons prefixRow (.cons upper (.cons lower suffix))

private theorem moved : Sheet.Move signature original sliced :=
  .under prefixRow (.split rowSplit suffix)

private def route : BoxAddress → BoxAddress := splitRoute 1 [(2, 0), (1, 0)]

private def made (row ordinal : ℕ) : BoxTrace signature :=
  ⟨Edge.source, [], [((), .box row ordinal 0)]⟩

private def sunk (name : WireOrigin) : BoxTrace signature :=
  ⟨Edge.sink, [((), name)], []⟩

private def scalar : BoxTrace signature := ⟨Edge.scalar, [], []⟩

/-- The decoder tracks both crossed names and the shifted suffix source. -/
example : original.traceWires =
    ⟨[[made 0 0], [scalar, made 1 1], [sunk (.box 0 0 0), sunk (.box 1 1 0), made 2 2]],
      [((), .box 2 2 0), ((), .boundary 0)]⟩ := rfl

example : sliced.traceWires =
    ⟨[[made 0 0], [made 1 0], [scalar], [sunk (.box 0 0 0), sunk (.box 1 0 0), made 3 2]],
      [((), .box 3 2 0), ((), .boundary 0)]⟩ := rfl

private theorem fixture_renamed : original.traceWires.Renamed sliced.traceWires route := by
  refine ⟨?_, rfl⟩
  exact (List.Perm.swap ((1, 0), made 1 0) ((2, 0), scalar) _).cons ((0, 0), made 0 0)

example : Set.BijOn route original.traceWires.boxAddresses sliced.traceWires.boxAddresses :=
  fixture_renamed.bijOn

example : sliced.traceWires.Renamed original.traceWires
    (Function.invFunOn route original.traceWires.boxAddresses) :=
  fixture_renamed.inverse

example : ∃ rename, sliced.traceWires.Renamed original.traceWires rename ∧
    Set.BijOn rename sliced.traceWires.boxAddresses original.traceWires.boxAddresses :=
  Sheet.SeamEquivalent.trace_incidence (.symm _ _ (.rel _ _ moved))

end Silmaril.RuntimeWires.Proofs.SeamTrace.Regression
