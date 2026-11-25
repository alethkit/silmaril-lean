module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Geometry
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Coordinates
public import Silmaril.Semantics.RuntimeWires.ProgressiveSweep.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveNullaryCrossing.Thms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
variable {lower : Diagram S L W .point} {upper : Diagram S R W .point}
variable (m : lower.VerticalMatch upper)

private theorem below_half {h : ℝ} (lt : h < 1) : halfHeight 0 h < 1 / 2 := by
  dsimp only [halfHeight]
  linarith

private theorem above_half {h : ℝ} (lt : 0 < h) : (1 / 2 : ℝ) < halfHeight 1 h := by
  dsimp only [halfHeight]
  linarith

theorem x_scaled_left (w : Fin W) {h : ℝ} (lt : h < 1) :
    m.glue.x w (halfHeight 0 h) = lower.x w h := by
  rw [m.glue_x_below w (below_half lt).le, unscale]

theorem x_scaled_right (w : Fin W) {h : ℝ} (lt : 0 < h) :
    m.glue.x w (halfHeight 1 h) = upper.x w h := by
  rw [m.glue_x_above w (above_half lt).le, unscale]

theorem active_left (w : Fin W) {h : ℝ} (lt : h < 1) :
    m.glue.crosses w (halfHeight 0 h) ↔ lower.crosses w h := by
  have last : lower.upper w = 1 := by simp [Diagram.upper, endpointHeight, m.lower_cap]
  have bound := (below_half lt).trans (m.crosses_join w).2
  change (m.glue.lower w < halfHeight 0 h ∧ halfHeight 0 h < m.glue.upper w) ↔
    lower.lower w < h ∧ h < lower.upper w
  rw [m.glue_lower, last, (halfHeight_strictMono 0).lt_iff_lt]
  exact ⟨fun h => ⟨h.1, lt⟩, fun h => ⟨h.1, bound⟩⟩

theorem active_right (w : Fin W) {h : ℝ} (lt : 0 < h) :
    m.glue.crosses w (halfHeight 1 h) ↔ upper.crosses w h := by
  have first : upper.lower w = 0 := by simp [Diagram.lower, endpointHeight, m.upper_cap]
  have bound := (m.crosses_join w).1.trans (above_half lt)
  change (m.glue.lower w < halfHeight 1 h ∧ halfHeight 1 h < m.glue.upper w) ↔
    upper.lower w < h ∧ h < upper.upper w
  rw [m.glue_upper, first, (halfHeight_strictMono 1).lt_iff_lt]
  exact ⟨fun h => ⟨lt, h.2⟩, fun h => ⟨bound, h.2⟩⟩

theorem cut_left {h : ℝ} {xs : List (Fin W)} (lt : h < 1) (cut : lower.OrderedCut h xs) :
    m.glue.OrderedCut (halfHeight 0 h) xs :=
  ⟨fun w => (cut.exact_wires w).trans (active_left m w lt).symm,
    cut.ordered.imp (fun {w z} order => by
      rw [x_scaled_left m w lt, x_scaled_left m z lt]
      exact order)⟩

theorem cut_right {h : ℝ} {xs : List (Fin W)} (lt : 0 < h) (cut : upper.OrderedCut h xs) :
    m.glue.OrderedCut (halfHeight 1 h) xs :=
  ⟨fun w => (cut.exact_wires w).trans (active_right m w lt).symm,
    cut.ordered.imp (fun {w z} order => by
      rw [x_scaled_right m w lt, x_scaled_right m z lt]
      exact order)⟩

theorem join_from_lower {h : ℝ} {xs : List (Fin W)} (cut : lower.OrderedCut h xs)
    (lt : h < 1) (all : ∀ w, w ∈ xs) : m.glue.OrderedCut (1 / 2) xs :=
  ⟨fun w => ⟨fun _ => m.crosses_join w, fun _ => all w⟩,
    (cut.output_boundary_order lt (fun w _ => m.lower_cap w)).imp (fun {w z} order => by
      rw [m.glue_x_below w le_rfl, m.glue_x_below z le_rfl]
      simpa only [show slabHeight 0 (1 / 2) = 1 by norm_num [slabHeight]] using order)⟩

theorem join_from_upper {h : ℝ} {xs : List (Fin W)} (cut : upper.OrderedCut h xs)
    (lt : 0 < h) (all : ∀ w, w ∈ xs) : m.glue.OrderedCut (1 / 2) xs :=
  ⟨fun w => ⟨fun _ => m.crosses_join w, fun _ => all w⟩,
    (cut.input_boundary_order lt (fun w _ => m.upper_cap w)).imp (fun {w z} order => by
      rw [m.glue_x_above w le_rfl, m.glue_x_above z le_rfl]
      simpa only [show slabHeight 1 (1 / 2) = 0 by norm_num [slabHeight]] using order)⟩

theorem join_regular : m.glue.Regular (1 / 2) := by
  refine ⟨by norm_num [Set.mem_Ioo], ?_⟩
  intro j
  induction j using Fin.addCases with
  | left v => rw [m.glue_height_left]; exact (below_half (lower.vertex_inside v).2.2).ne
  | right v => rw [m.glue_height_right]; exact (above_half (upper.vertex_inside v).2.1).ne'

/-- A lower-slab event whose outgoing cut reads the gluing boundary. -/
def event_left {j : Fin L} {a b : ℝ} (e : lower.EventSlice j a b)
    (before : a < 1) (after : b < 1) (all : ∀ w, w ∈ e.afterWires) :
    m.glue.EventSlice (Fin.castAdd R j) (halfHeight 0 a) (1 / 2) where
  left := e.left
  right := e.right
  left_exact w := by
    rw [m.glue_height_left, m.glue_x_left, active_left m w (lower.vertex_inside j).2.2,
      x_scaled_left m w (lower.vertex_inside j).2.2]
    exact e.left_exact w
  right_exact w := by
    rw [m.glue_height_left, m.glue_x_left, active_left m w (lower.vertex_inside j).2.2,
      x_scaled_left m w (lower.vertex_inside j).2.2]
    exact e.right_exact w
  before := by rw [m.glue_inputs_left]; exact cut_left m before e.before
  after := by rw [m.glue_outputs_left]; exact join_from_lower m e.after after all

/-- An upper-slab event whose incoming cut reads the gluing boundary. -/
def event_right {j : Fin R} {a b : ℝ} (e : upper.EventSlice j a b)
    (before : 0 < a) (after : 0 < b) (all : ∀ w, w ∈ e.beforeWires) :
    m.glue.EventSlice (Fin.natAdd L j) (1 / 2) (halfHeight 1 b) where
  left := e.left
  right := e.right
  left_exact w := by
    rw [m.glue_height_right, m.glue_x_right, active_right m w (upper.vertex_inside j).2.1,
      x_scaled_right m w (upper.vertex_inside j).2.1]
    exact e.left_exact w
  right_exact w := by
    rw [m.glue_height_right, m.glue_x_right, active_right m w (upper.vertex_inside j).2.1,
      x_scaled_right m w (upper.vertex_inside j).2.1]
    exact e.right_exact w
  before := by rw [m.glue_inputs_right]; exact join_from_upper m e.before before all
  after := by rw [m.glue_outputs_right]; exact cut_right m after e.after

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
