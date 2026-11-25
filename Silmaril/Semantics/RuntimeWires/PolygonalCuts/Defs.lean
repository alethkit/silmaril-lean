module

public import Silmaril.Semantics.RuntimeWires.Polygonal.Layout

@[expose] public section

/-!
# Interior cuts of affine connectors

A cut refines the slabs of a fixed drawing without moving any points. The
setting is the polygonal realization for Definition 3.2 and Figure 7 of
Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal
Categories*, arXiv:2305.06075v5, pp. 9:6–9:7. The comparison in Lemma 3.4,
Theorem 3.6, and Corollary 3.15 also requires results about plane embeddings
and isotopy.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Polygonal

/-- A height strictly between the two caps of a slab. -/
structure Slab.Cut (slab : Slab) where
  height : ℝ
  above_lower : slab.lower < height
  below_upper : height < slab.upper

namespace Slab.Cut

variable {slab : Slab}

def lower (c : slab.Cut) : Slab := ⟨slab.lower, c.height, c.above_lower⟩

def upper (c : slab.Cut) : Slab := ⟨c.height, slab.upper, c.below_upper⟩

/-- The affine coordinate of the cut height in the original slab. -/
noncomputable def parameter (c : slab.Cut) : ℝ :=
  (c.height - slab.lower) / (slab.upper - slab.lower)

theorem parameter_pos (c : slab.Cut) : 0 < c.parameter :=
  div_pos (sub_pos.mpr c.above_lower) (sub_pos.mpr slab.increasing)

theorem parameter_lt_one (c : slab.Cut) : c.parameter < 1 :=
  (div_lt_one (sub_pos.mpr slab.increasing)).mpr (sub_lt_sub_right c.below_upper _)

/-- The horizontal coordinate where a strand crosses the cut. -/
noncomputable def coordinate (c : slab.Cut) (s : Strand slab) : ℝ :=
  interpolate s.start s.finish c.parameter

noncomputable def lowerStrand (c : slab.Cut) (s : Strand slab) : Strand c.lower :=
  ⟨s.start, c.coordinate s⟩

noncomputable def upperStrand (c : slab.Cut) (s : Strand slab) : Strand c.upper :=
  ⟨c.coordinate s, s.finish⟩

/-- The typed ports at the cut, indexed in the order of the original connector. -/
noncomputable def frontier {O : Type*} {A : List O} (c : slab.Cut) (p q : Frontier A) :
    Frontier A :=
  Frontier.ofCoordinates (fun i => c.coordinate (connector slab p q i)) (by
    intro i j hij
    exact add_lt_add
      (mul_lt_mul_of_pos_left ((List.pairwise_iff_get.mp p.ordered) _ _ hij)
        (sub_pos.mpr c.parameter_lt_one))
      (mul_lt_mul_of_pos_left ((List.pairwise_iff_get.mp q.ordered) _ _ hij) c.parameter_pos))

end Slab.Cut
end Silmaril.RuntimeWires.Polygonal
