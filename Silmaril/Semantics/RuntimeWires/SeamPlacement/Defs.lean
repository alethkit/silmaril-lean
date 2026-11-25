module

public import Silmaril.Semantics.RuntimeWires.SlicedTrace.Defs

@[expose] public section

/-!
# Placement beside a through strand

A scalar on either side of a strand gives a test for whether decoded
incidence distinguishes the combinatorial seam classes. The relevant
diagrammatic operations are illustrated in Definition 3.2 and Figure 7
(pp. 9:6–9:7) of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

/-- Count the boxes before the first through cell. If there is no through
cell, count the entire row. -/
def Row.boxesBeforeFirstWire : {A B : List O} → Row S A B → ℕ
  | _, _, .empty => 0
  | _, _, .wire _ _ => 0
  | _, _, .box _ rest => rest.boxesBeforeFirstWire + 1

/-- If each row has the same single through strand, this counts precisely
the boxes on its left over the whole sheet. -/
def Sheet.boxesBeforeFirstWire : {A B : List O} → Sheet S A B → ℕ
  | _, _, .empty _ => 0
  | _, _, .cons row rest => row.boxesBeforeFirstWire + rest.boxesBeforeFirstWire

namespace NullaryPlacement

/-- A single wire type and a single generator with no ports. -/
abbrev signature : Signature Unit where
  Edge := Unit
  source _ := []
  target _ := []

/-- The scalar lies to the left of the boundary-to-boundary wire. -/
def scalarLeft : Sheet signature [()] [()] :=
  .cons (Row.box (S := signature) () (.wire () .empty)) (.empty _)

/-- The same scalar lies to the right of the boundary-to-boundary wire. -/
def scalarRight : Sheet signature [()] [()] :=
  .cons (.wire () (Row.box (S := signature) () .empty)) (.empty _)

end NullaryPlacement
end Silmaril.RuntimeWires.Sliced
