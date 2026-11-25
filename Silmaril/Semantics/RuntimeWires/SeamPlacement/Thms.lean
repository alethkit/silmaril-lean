module

public import Silmaril.Semantics.RuntimeWires.SeamPlacement.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.SeamPlacement.Invariant

public section

namespace Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

/-- In an all-nullary signature each row retains its entire ordered wire
word. In particular a singleton input remains a single through strand. -/
theorem Row.boundary_eq_of_nullary {A B : List O} (r : Row S A B)
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) : A = B :=
  Proofs.SeamPlacement.row_boundary r nullary

/-- The two split rows account for the original number of boxes before
the first through strand. -/
theorem Row.Split.boxesBeforeFirstWire_add {A M B : List O}
    {r : Row S A B} {p : Row S A M} {q : Row S M B} (split : Row.Split S r p q)
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) :
    r.boxesBeforeFirstWire = p.boxesBeforeFirstWire + q.boxesBeforeFirstWire :=
  Proofs.SeamPlacement.split_count split nullary

theorem Sheet.Move.boxesBeforeFirstWire_eq {A B : List O} {p q : Sheet S A B}
    (move : Sheet.Move S p q) (nullary : ∀ e, S.source e = [] ∧ S.target e = []) :
    p.boxesBeforeFirstWire = q.boxesBeforeFirstWire :=
  Proofs.SeamPlacement.move_count move nullary

theorem Sheet.SeamEquivalent.boxesBeforeFirstWire_eq {A B : List O} {p q : Sheet S A B}
    (same : Sheet.SeamEquivalent p q) (nullary : ∀ e, S.source e = [] ∧ S.target e = []) :
    p.boxesBeforeFirstWire = q.boxesBeforeFirstWire :=
  Proofs.SeamPlacement.seam_count same nullary

namespace NullaryPlacement

/-- The scalar is recorded without ports and the strand keeps the input
cap name at output slot zero. -/
theorem scalarLeft_trace : scalarLeft.traceWires =
    ⟨[[⟨(), [], []⟩]], [((), .boundary 0)]⟩ := rfl

/-- Both sheets decode to the same labeled generator, empty port lists,
and the same boundary-to-boundary wire. -/
theorem trace_eq : scalarLeft.traceWires = scalarRight.traceWires := rfl

/-- The seam rules cannot move the scalar across the through strand. -/
theorem not_seamEquivalent : ¬ Sheet.SeamEquivalent scalarLeft scalarRight :=
  Proofs.SeamPlacement.counterexample

end NullaryPlacement
end Silmaril.RuntimeWires.Sliced
