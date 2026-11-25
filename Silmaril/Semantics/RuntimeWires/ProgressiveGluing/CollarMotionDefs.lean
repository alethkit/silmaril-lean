module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarDefs

@[expose] public section

/-!
# Moving the strands of a fixed-cap collar

Definition 3.2 and the sequential juxtaposition in Lemma 3.4 and Figure 7
are from Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal
Categories*, arXiv:2305.06075v5 (pp. 9:6–9:7).

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u

/-- Vertex-free polygonal strands with the prescribed endpoint numbers,
labels, coordinates and horizontal order. -/
structure PolygonalCollar {O : Type u} {W : ℕ} (cap : CollarSpec O W) where
  wire : Fin W → Wire 0 1
  bottom : ∀ w, (wire w).x 0 = cap.bottom w
  top : ∀ w, (wire w).x 1 = cap.top w
  inside : ∀ w y, y ∈ Set.Icc (0 : ℝ) 1 → (wire w).x y ∈ Set.Ioo 0 1
  ordered : ∀ a b y, y ∈ Set.Icc (0 : ℝ) 1 → cap.bottom a < cap.bottom b →
    (wire a).x y < (wire b).x y

namespace PolygonalCollar

/-- The time parameter used for progressive paths. -/
abbrev Time := Set.Icc (0 : ℝ) 1

/-- A finite set of heights subordinate to the affine pieces of a wire. -/
def Subdivides (w : Wire 0 1) (knots : Finset ℝ) : Prop :=
  ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
    a < b → (∀ k ∈ knots, k ∉ Set.Ioo a b) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
    w.x ((1 - t) * a + t * b) = (1 - t) * w.x a + t * w.x b

end PolygonalCollar
end Silmaril.RuntimeWires.ProgressiveGraph
