module

public import Silmaril.Semantics.RuntimeWires.SeamPlacement.Defs
public import Mathlib.Data.Multiset.Defs

@[expose] public section

/-!
# Gap labels for sheets of nullary generators

This gives a restricted classification of combinatorial seam classes in
the setting of Definition 3.2, Figure 7 and Lemma 3.4 (pp. 9:6–9:7) of
Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal
Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

/-- Read the box labels after exactly the given number of through cells.
Gap zero precedes all through cells. -/
def Row.labelsInGap : {A B : List O} → Row S A B → ℕ → List S.Edge
  | _, _, .empty, _ => []
  | _, _, .wire _ _, 0 => []
  | _, _, .wire _ rest, gap + 1 => rest.labelsInGap gap
  | _, _, .box e rest, 0 => e :: rest.labelsInGap 0
  | _, _, .box _ rest, gap + 1 => rest.labelsInGap (gap + 1)

/-- For an all-nullary signature the same ordered strands persist in every
row. This reads one gap in row order and preserves repeated labels. -/
def Sheet.labelsInGap : {A B : List O} → Sheet S A B → ℕ → List S.Edge
  | _, _, .empty _, _ => []
  | _, _, .cons row rest, gap => row.labelsInGap gap ++ rest.labelsInGap gap

/-- The label multiset in each gap, including the two exterior gaps. For
the empty boundary word there is one gap. -/
def Sheet.gapMultisets {A B : List O} (p : Sheet S A B) (gap : Fin (A.length + 1)) :
    Multiset S.Edge :=
  p.labelsInGap gap.val

end Silmaril.RuntimeWires.Sliced
