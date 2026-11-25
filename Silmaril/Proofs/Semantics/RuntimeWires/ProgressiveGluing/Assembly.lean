module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Drawing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
variable {lower : Diagram S L W .point} {upper : Diagram S R W .point}
variable (m : lower.VerticalMatch upper)

theorem input_order (j : Fin (L + R)) {i k : Fin (S.source (gluedGenerator lower upper j)).length}
    (order : i < k) {y : ℝ}
    (lowi : jointLower lower upper (ports S.source lower.input upper.input j i) < y)
    (lowk : jointLower lower upper (ports S.source lower.input upper.input j k) < y)
    (high : y < gluedHeight lower upper j) :
    (gluedWire m (ports S.source lower.input upper.input j i)).x y <
      (gluedWire m (ports S.source lower.input upper.input j k)).x y := by
  induction j using Fin.addCases with
  | left v =>
    let idx := i.cast (congrArg (fun e => (S.source e).length) (generator_left v))
    exact (input_left_empty m v idx).elim
  | right v =>
    let first := i.cast (congrArg (fun e => (S.source e).length) (generator_right v))
    let second := k.cast (congrArg (fun e => (S.source e).length) (generator_right v))
    rw [ports_right] at lowi lowk
    rw [height_right] at high
    rw [ports_right, ports_right]
    change jointLower lower upper (upper.input v first) < y at lowi
    change jointLower lower upper (upper.input v second) < y at lowk
    change (gluedWire m (upper.input v first)).x y < (gluedWire m (upper.input v second)).x y
    let sample := halfHeight 1 (upper.vertexHeight v / 2)
    have pos := (upper.vertex_inside v).2.1
    have above : 1 / 2 < sample := by dsimp [sample, halfHeight]; linarith
    have below : sample < halfHeight 1 (upper.vertexHeight v) :=
      halfHeight_strictMono 1 (by linarith)
    have active (idx : Fin (S.source (upper.generator v)).length) {h : ℝ}
        (lo : jointLower lower upper (upper.input v idx) < h)
        (hi : h < halfHeight 1 (upper.vertexHeight v)) :
        h ∈ Set.Ioo (jointLower lower upper (upper.input v idx)) (jointUpper lower upper (upper.input v idx)) := by
      refine ⟨lo, ?_⟩
      have attached := (upper.input_exact v _).mpr ⟨idx, rfl⟩
      change h < endpointHeight (gluedHeight lower upper) 1 (gluedFinish upper (upper.input v idx))
      rw [high_bound]
      simpa [Diagram.upper, endpointHeight, attached] using hi
    refine transport_order m (active first ((join_inside m _).1.trans above) below)
      (active second ((join_inside m _).1.trans above) below) (active first lowi high) (active second lowk high) ?_
    rw [wire_right m _ above.le, wire_right m _ above.le]
    change upper.x (upper.input v first) (slabHeight 1 (halfHeight 1 (upper.vertexHeight v / 2))) < _
    rw [unscale]
    exact upper.input_order v order
      (by simp [endpointHeight, m.upper_cap]; linarith) (by simp [endpointHeight, m.upper_cap]; linarith) (by linarith)

theorem output_order (j : Fin (L + R)) {i k : Fin (S.target (gluedGenerator lower upper j)).length}
    (order : i < k) {y : ℝ}
    (low : gluedHeight lower upper j < y)
    (hii : y < jointUpper lower upper (ports S.target lower.output upper.output j i))
    (hik : y < jointUpper lower upper (ports S.target lower.output upper.output j k)) :
    (gluedWire m (ports S.target lower.output upper.output j i)).x y <
      (gluedWire m (ports S.target lower.output upper.output j k)).x y := by
  induction j using Fin.addCases with
  | right v =>
    let idx := i.cast (congrArg (fun e => (S.target e).length) (generator_right v))
    exact (output_right_empty m v idx).elim
  | left v =>
    let first := i.cast (congrArg (fun e => (S.target e).length) (generator_left v))
    let second := k.cast (congrArg (fun e => (S.target e).length) (generator_left v))
    rw [ports_left] at hii hik
    rw [height_left] at low
    rw [ports_left, ports_left]
    change y < jointUpper lower upper (lower.output v first) at hii
    change y < jointUpper lower upper (lower.output v second) at hik
    change (gluedWire m (lower.output v first)).x y < (gluedWire m (lower.output v second)).x y
    let sample := halfHeight 0 ((lower.vertexHeight v + 1) / 2)
    have ltOne := (lower.vertex_inside v).2.2
    have below : sample < 1 / 2 := by dsimp [sample, halfHeight]; linarith
    have above : halfHeight 0 (lower.vertexHeight v) < sample :=
      halfHeight_strictMono 0 (by linarith)
    have active (idx : Fin (S.target (lower.generator v)).length) {h : ℝ}
        (lo : halfHeight 0 (lower.vertexHeight v) < h)
        (hi : h < jointUpper lower upper (lower.output v idx)) :
        h ∈ Set.Ioo (jointLower lower upper (lower.output v idx)) (jointUpper lower upper (lower.output v idx)) := by
      refine ⟨?_, hi⟩
      have attached := (lower.output_exact v _).mpr ⟨idx, rfl⟩
      change endpointHeight (gluedHeight lower upper) 0 (gluedStart lower (lower.output v idx)) < h
      rw [low_bound]
      simpa [Diagram.lower, endpointHeight, attached] using lo
    refine transport_order m (active first above (below.trans (join_inside m _).2))
      (active second above (below.trans (join_inside m _).2)) (active first low hii) (active second low hik) ?_
    rw [wire_left m _ below.le, wire_left m _ below.le]
    change lower.x (lower.output v first) (slabHeight 0 (halfHeight 0 ((lower.vertexHeight v + 1) / 2))) < _
    rw [unscale]
    exact lower.output_order v order (by linarith)
      (by simp [endpointHeight, m.lower_cap]; linarith) (by simp [endpointHeight, m.lower_cap]; linarith)

/-- The combined drawing uses the disjoint union of the old vertex IDs.
Every wire ID represents one spliced strand. -/
noncomputable def assemble : Diagram S (L + R) W .point where
  vertexX := gluedVertexX lower upper
  vertexHeight := gluedHeight lower upper
  vertex_inside := vertex_inside
  vertex_separation := vertex_separation
  generator := gluedGenerator lower upper
  label := lower.label
  start := gluedStart lower
  finish := gluedFinish upper
  wire := gluedWire m
  wire_inside := wire_inside m
  start_attached := start_attached m
  finish_attached := finish_attached m
  separated := separated_wires m
  avoids_vertex := avoids_vertex m
  input_boundary_separated := by
    intro w z different aw az
    rw [wire_left m w (by norm_num), wire_left m z (by norm_num)]
    simpa only [Diagram.x, show slabHeight 0 0 = 0 by norm_num [slabHeight]] using
      lower.input_boundary_separated different (by simpa [gluedStart] using aw)
        (by simpa [gluedStart] using az)
  output_boundary_separated := by
    intro w z different aw az
    rw [wire_right m w (by norm_num), wire_right m z (by norm_num)]
    simpa only [Diagram.x, show slabHeight 1 1 = 1 by norm_num [slabHeight]] using
      upper.output_boundary_separated different (by simpa [gluedFinish] using aw)
        (by simpa [gluedFinish] using az)
  input := ports S.source lower.input upper.input
  output := ports S.target lower.output upper.output
  input_exact := input_exact m
  output_exact := output_exact m
  input_types := input_types m
  output_types := output_types m
  input_order := input_order m
  output_order := output_order m

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
