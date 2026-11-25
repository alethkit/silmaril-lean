module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Partial
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepRows

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.ProgressiveGluing

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)

theorem sweepStack : LevelStack lower upper m.glue :=
  ⟨m.glue_height_lower, m.glue_height_upper⟩

private theorem crosses_lower {h : ℝ} (below : h < 1) (z : Fin (wireCount lower upper)) :
    m.glue.crosses z (halfHeight 0 h) ↔ ∃ w, lower.crosses w h ∧ lowerId w = z := by
  obtain ⟨ws, cut⟩ := lower.ordered_cut_exists h
  simp only [← (m.cut_lower below cut).exact_wires z, List.mem_map, cut.exact_wires]

private theorem crosses_upper {h : ℝ} (above : 0 < h) (z : Fin (wireCount lower upper)) :
    m.glue.crosses z (halfHeight 1 h) ↔ ∃ w, upper.crosses w h ∧ m.upperId w = z := by
  obtain ⟨ws, cut⟩ := upper.ordered_cut_exists h
  simp only [← (m.cut_upper above cut).exact_wires z, List.mem_map, cut.exact_wires]

theorem slots_lower {h a b k c d : ℝ} (height : k = halfHeight 0 h) (below : h < 1)
    (p : lower.LayerSlice h a b) (s : m.glue.LayerSlice k c d) :
    s.slots = p.slots.map (Sum.map lowerId (Fin.castAdd R)) := by
  subst k
  apply slots_image p s
  · intro slot
    cases slot with
    | inl w =>
      change m.glue.x (lowerId w) (halfHeight 0 h) = lower.x w h
      rw [m.glue_x_lower w (halfHeight_below below).le, unscale]
    | inr v => exact m.glue_vertexX_lower v
  · intro slot
    cases slot with
    | inl w =>
      change m.glue.crosses (lowerId w) (halfHeight 0 h) ↔ lower.crosses w h
      rw [crosses_lower m below]
      exact ⟨fun ⟨z, active, eq⟩ => (lowerId_injective (lower := lower) (upper := upper) eq) ▸ active, fun active => ⟨w, active, rfl⟩⟩
    | inr v =>
      change m.glue.vertexHeight (Fin.castAdd R v) = halfHeight 0 h ↔ lower.vertexHeight v = h
      rw [m.glue_height_lower, (halfHeight_strictMono 0).injective.eq_iff]
  · intro slot hs
    cases slot with
    | inl z =>
      obtain ⟨w, _, eq⟩ := (crosses_lower m below z).mp hs
      exact ⟨.inl w, congrArg Sum.inl eq⟩
    | inr v =>
      induction v using Fin.addCases with
      | left v => exact ⟨.inr v, rfl⟩
      | right v =>
        change m.glue.vertexHeight (Fin.natAdd L v) = halfHeight 0 h at hs
        rw [m.glue_height_upper] at hs
        exact (((halfHeight_below below).trans (halfHeight_above (upper.vertex_inside v).2.1)).ne hs.symm).elim

theorem slots_upper {h a b k c d : ℝ} (height : k = halfHeight 1 h) (above : 0 < h)
    (q : upper.LayerSlice h a b) (s : m.glue.LayerSlice k c d) :
    s.slots = q.slots.map (Sum.map m.upperId (Fin.natAdd L)) := by
  subst k
  apply slots_image q s
  · intro slot
    cases slot with
    | inl w =>
      change m.glue.x (m.upperId w) (halfHeight 1 h) = upper.x w h
      rw [m.glue_x_upper w (halfHeight_above above).le, unscale]
    | inr v => exact m.glue_vertexX_upper v
  · intro slot
    cases slot with
    | inl w =>
      change m.glue.crosses (m.upperId w) (halfHeight 1 h) ↔ upper.crosses w h
      rw [crosses_upper m above]
      exact ⟨fun ⟨z, active, eq⟩ => m.upperId_injective eq ▸ active, fun active => ⟨w, active, rfl⟩⟩
    | inr v =>
      change m.glue.vertexHeight (Fin.natAdd L v) = halfHeight 1 h ↔ upper.vertexHeight v = h
      rw [m.glue_height_upper, (halfHeight_strictMono 1).injective.eq_iff]
  · intro slot hs
    cases slot with
    | inl z =>
      obtain ⟨w, _, eq⟩ := (crosses_upper m above z).mp hs
      exact ⟨.inl w, congrArg Sum.inl eq⟩
    | inr v =>
      induction v using Fin.addCases with
      | left v =>
        change m.glue.vertexHeight (Fin.castAdd R v) = halfHeight 1 h at hs
        rw [m.glue_height_lower] at hs
        exact (((halfHeight_below (lower.vertex_inside v).2.2).trans (halfHeight_above above)).ne hs).elim
      | right v => exact ⟨.inr v, rfl⟩

theorem row_cells_lower (p : lower.LayerSweep) (s : m.glue.LayerSweep) (i : Fin lower.levelCount) :
    (s.row ((sweepStack m).lowerLevel i)).cells = (p.row i).cells := by
  rw [sweep_row_cells, sweep_row_cells]
  have below : lower.levelHeight i < 1 := (p.layer i).isolation.above.trans (p.layer i).isolation.hi_inside
  rw [slots_lower m ((sweepStack m).height_lower i) below (p.layer i)]
  exact layerRow_cells_image lowerId (Fin.castAdd R) m.glue_label_lower m.glue_generator_lower _

theorem row_cells_upper (q : upper.LayerSweep) (s : m.glue.LayerSweep) (i : Fin upper.levelCount) :
    (s.row ((sweepStack m).upperLevel i)).cells = (q.row i).cells := by
  rw [sweep_row_cells, sweep_row_cells]
  have above : 0 < upper.levelHeight i := (q.layer i).isolation.lo_inside.trans (q.layer i).isolation.below
  rw [slots_upper m ((sweepStack m).height_upper i) above (q.layer i)]
  exact layerRow_cells_image m.upperId (Fin.natAdd L) m.glue_label_upper m.glue_generator_upper _

end Silmaril.RuntimeWires.Proofs.PartialGluing
