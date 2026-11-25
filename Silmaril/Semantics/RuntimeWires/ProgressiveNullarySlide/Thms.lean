module

public import Silmaril.Semantics.RuntimeWires.ProgressiveNullarySlide.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveSimultaneous.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveNullarySlide.Frames

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.NullarySlide

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable {d : Diagram S V W .point} {moved : Fin V} (s : d.NullarySlide moved)

theorem height_mem (t : Time) : s.heightAt t ∈ Set.Icc s.bottom s.top :=
  Proofs.ProgressiveNullarySlide.height_mem s t

/-- Change the height of the scalar with the labels and ordered ports held fixed. -/
@[expose] def atHeight (h : ℝ) (within : h ∈ Set.Icc s.bottom s.top) : Diagram S V W .point :=
  s.assemble h (by exact Proofs.ProgressiveNullarySlide.frame_conditions s h within)

/-- Every time is a valid progressive polygonal embedding of the same graph. -/
@[expose] def frame (t : Time) : Diagram S V W .point := s.atHeight (s.heightAt t) (s.height_mem t)

/-- The initial and terminal diagrams are specified directly by their coordinates. -/
@[expose] def initial : Diagram S V W .point :=
  s.atHeight s.bottom ⟨le_rfl, s.ordered.le⟩

@[expose] def terminal : Diagram S V W .point :=
  s.atHeight s.top ⟨s.ordered.le, le_rfl⟩

theorem moved_height {h : ℝ} (within : h ∈ Set.Icc s.bottom s.top) :
    (s.atHeight h within).vertexHeight moved = h := by
  change s.heights h moved = h
  simp [heights]

theorem stationary_height {h : ℝ} (within : h ∈ Set.Icc s.bottom s.top) {v : Fin V}
    (other : v ≠ moved) : (s.atHeight h within).vertexHeight v = d.vertexHeight v := by
  change s.heights h v = d.vertexHeight v
  simp [heights, other]

/-- All coordinates of the wire paths, including cap points, remain fixed. -/
theorem wire_point {h : ℝ} (within : h ∈ Set.Icc s.bottom s.top) (w : Fin W) (y : ℝ) :
    ((s.atHeight h within).wire w).point y = (d.wire w).point y := rfl

theorem lower_eq {h : ℝ} (within : h ∈ Set.Icc s.bottom s.top) (w : Fin W) :
    (s.atHeight h within).lower w = d.lower w :=
  Proofs.ProgressiveNullarySlide.start_height s h w

theorem upper_eq {h : ℝ} (within : h ∈ Set.Icc s.bottom s.top) (w : Fin W) :
    (s.atHeight h within).upper w = d.upper w :=
  Proofs.ProgressiveNullarySlide.finish_height s h w

/-- Each full wire trace and therefore every cap contact remains fixed. -/
theorem wire_trace {h : ℝ} (within : h ∈ Set.Icc s.bottom s.top) (w : Fin W) :
    ((s.atHeight h within).wire w).trace = (d.wire w).trace := by
  change (((s.atHeight h within).wire w).point '' Set.Icc ((s.atHeight h within).lower w)
    ((s.atHeight h within).upper w)) = (d.wire w).point '' Set.Icc (d.lower w) (d.upper w)
  rw [s.lower_eq within w, s.upper_eq within w, funext (s.wire_point within w)]

/-- All frames have the same ordered wire-ID list at any fixed height. -/
theorem ordered_cut_iff {h : ℝ} (within : h ∈ Set.Icc s.bottom s.top) {y : ℝ} {ws : List (Fin W)} :
    (s.atHeight h within).OrderedCut y ws ↔ d.OrderedCut y ws :=
  Proofs.ProgressiveNullarySlide.ordered_cut_iff s within

/-- The vertex trajectories are continuous. Each wire parametrization is
constant in time and continuous on its original closed height interval. -/
theorem continuous_vertex (v : Fin V) :
    Continuous (fun t : Time => ((s.frame t).vertexX v, (s.frame t).vertexHeight v)) :=
  Proofs.ProgressiveNullarySlide.continuous_vertex s v

theorem continuous_wire (w : Fin W) :
    Continuous (fun p : Time × Set.Icc (d.lower w) (d.upper w) => ((s.frame p.1).wire w).point p.2.val) :=
  Proofs.ProgressiveNullarySlide.continuous_wire s w

theorem frame_start : s.frame ⟨0, le_rfl, zero_le_one⟩ = s.initial :=
  Proofs.ProgressiveNullarySlide.frame_start s

theorem frame_finish : s.frame ⟨1, zero_le_one, le_rfl⟩ = s.terminal :=
  Proofs.ProgressiveNullarySlide.frame_finish s

theorem height_strict : StrictMono s.heightAt :=
  Proofs.ProgressiveNullarySlide.height_strict s

/-- A scalar on the left of an isolated stationary vertex crosses its height
at exactly one time. The tied frame admits the existing geometric pair slice. -/
theorem isolated_crossing {other : Fin V} {lo hi : ℝ}
    (horizontal : d.vertexX moved < d.vertexX other)
    (crosses : d.vertexHeight other ∈ Set.Ioo s.bottom s.top)
    (lo_inside : 0 < lo) (lo_bottom : lo < s.bottom)
    (top_hi : s.top < hi) (hi_inside : hi < 1)
    (only : ∀ v, d.vertexHeight v ∈ Set.Icc lo hi → v = moved ∨ v = other) :
    ∃! t : Time, (s.frame t).IsolatesPair moved other lo hi :=
  Proofs.ProgressiveNullarySlide.isolated_crossing s horizontal crosses lo_inside lo_bottom
    top_hi hi_inside only

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.NullarySlide
