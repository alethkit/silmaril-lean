module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Defs

@[expose] public section

/-!
# Sliding an isolated nullary vertex

A point-vertex deformation for Definition 3.2 and Figure 7 of Mario Román and
Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5, pp. 9:6–9:7. The data are geometric and can be given
before making any cuts.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}

/-- The scalar may travel along a closed vertical segment in the open square.
The entire segment must avoid the wire traces and the other vertices. -/
structure NullarySlide (d : Diagram S V W .point) (moved : Fin V) where
  bottom : ℝ
  top : ℝ
  bottom_pos : 0 < bottom
  ordered : bottom < top
  top_lt_one : top < 1
  original : d.vertexHeight moved ∈ Set.Icc bottom top
  no_inputs : S.source (d.generator moved) = []
  no_outputs : S.target (d.generator moved) = []
  wire_clear : ∀ w h, h ∈ Set.Icc bottom top → d.covers w h → d.x w h ≠ d.vertexX moved
  vertex_clear : ∀ v, v ≠ moved → d.vertexHeight v ∈ Set.Icc bottom top →
    d.vertexX v ≠ d.vertexX moved

namespace NullarySlide

variable {d : Diagram S V W .point} {moved : Fin V} (s : d.NullarySlide moved)

abbrev Time := Set.Icc (0 : ℝ) 1

/-- Linear motion of the scalar along the empty segment. -/
def heightAt (t : Time) : ℝ := (1 - t.val) * s.bottom + t.val * s.top

/-- Only the moved vertex changes height. -/
def heights (_s : d.NullarySlide moved) (h : ℝ) (v : Fin V) : ℝ := if v = moved then h else d.vertexHeight v

/-- The geometric checks needed to reuse all original strands at new vertex heights. -/
structure FrameConditions (h : ℝ) : Prop where
  inside : ∀ v, s.heights h v ∈ Set.Ioo 0 1
  injective_points : Function.Injective (fun v => (d.vertexX v, s.heights h v))
  start_height : ∀ w, endpointHeight (s.heights h) 0 (d.start w) =
    endpointHeight d.vertexHeight 0 (d.start w)
  finish_height : ∀ w, endpointHeight (s.heights h) 1 (d.finish w) =
    endpointHeight d.vertexHeight 1 (d.finish w)
  avoids : ∀ w v, d.crosses w (s.heights h v) → d.x w (s.heights h v) ≠ d.vertexX v

/-- Keep all wire coordinates and port lists, using the unchanged endpoint heights
at the new vertex coordinates. -/
def assemble (h : ℝ) (ok : s.FrameConditions h) : Diagram S V W .point where
  vertexX := d.vertexX
  vertexHeight := s.heights h
  vertex_inside v := ⟨(d.vertex_inside v).1, ok.inside v⟩
  vertex_separation := ok.injective_points
  generator := d.generator
  label := d.label
  start := d.start
  finish := d.finish
  wire w := {
    x := (d.wire w).x
    increasing := by simpa only [ok.start_height, ok.finish_height] using (d.wire w).increasing
    continuous := by simpa only [ok.start_height, ok.finish_height] using (d.wire w).continuous
    polygonal := by simpa only [ok.start_height, ok.finish_height] using (d.wire w).polygonal }
  wire_inside w y hy := d.wire_inside w y (by simpa only [ok.start_height, ok.finish_height] using hy)
  start_attached w v eq := by
    have same := ok.start_height w
    rw [eq] at same
    change s.heights h v = d.vertexHeight v at same
    change (d.wire w).x (s.heights h v) = d.vertexX v
    rw [same]
    exact d.start_attached w v eq
  finish_attached w v eq := by
    have same := ok.finish_height w
    rw [eq] at same
    change s.heights h v = d.vertexHeight v at same
    change (d.wire w).x (s.heights h v) = d.vertexX v
    rw [same]
    exact d.finish_attached w v eq
  separated := by
    intro w z different y inner closed
    exact d.separated different (h := y) (by simpa only [ok.start_height, ok.finish_height] using inner)
      (by simpa only [ok.start_height, ok.finish_height] using closed)
  avoids_vertex w v inner := ok.avoids w v (by
    simpa only [Diagram.crosses, Diagram.lower, Diagram.upper, ok.start_height, ok.finish_height] using inner)
  input_boundary_separated := d.input_boundary_separated
  output_boundary_separated := d.output_boundary_separated
  input := d.input
  output := d.output
  input_exact := d.input_exact
  output_exact := d.output_exact
  input_types := d.input_types
  output_types := d.output_types
  input_order v {i j} ij {y} first second above := by
    have same := ok.finish_height (d.input v i)
    rw [(d.input_exact v _).mpr ⟨i, rfl⟩] at same
    change s.heights h v = d.vertexHeight v at same
    exact d.input_order v ij (by simpa only [ok.start_height] using first)
      (by simpa only [ok.start_height] using second) (same ▸ above)
  output_order v {i j} ij {y} below first second := by
    have same := ok.start_height (d.output v i)
    rw [(d.output_exact v _).mpr ⟨i, rfl⟩] at same
    change s.heights h v = d.vertexHeight v at same
    exact d.output_order v ij (same ▸ below)
      (by simpa only [ok.finish_height] using first) (by simpa only [ok.finish_height] using second)

end NullarySlide
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
