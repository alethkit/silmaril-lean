module

public import Silmaril.Semantics.RuntimeWires.ProgressiveNullarySlide.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Silmaril.Semantics.RuntimeWires.ProgressiveSimultaneous.Defs

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveNullarySlide

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable {d : Diagram S V W .point} {moved : Fin V} (s : d.NullarySlide moved)

theorem height_mem (t : NullarySlide.Time) : s.heightAt t ∈ Set.Icc s.bottom s.top := by
  have delta := sub_pos.mpr s.ordered
  have low := mul_nonneg t.property.1 delta.le
  have high := mul_nonneg (sub_nonneg.mpr t.property.2) delta.le
  constructor <;> unfold NullarySlide.heightAt <;> nlinarith only [low, high]

include s in
theorem no_start (w : Fin W) : d.start w ≠ some moved := by
  intro eq
  obtain ⟨i, _⟩ := (d.output_exact moved w).mp eq
  simpa [s.no_outputs] using i.isLt

include s in
theorem no_finish (w : Fin W) : d.finish w ≠ some moved := by
  intro eq
  obtain ⟨i, _⟩ := (d.input_exact moved w).mp eq
  simpa [s.no_inputs] using i.isLt

theorem start_height (h : ℝ) (w : Fin W) :
    endpointHeight (s.heights h) 0 (d.start w) = endpointHeight d.vertexHeight 0 (d.start w) := by
  cases eq : d.start w with
  | none => simp [endpointHeight]
  | some v =>
    have different : v ≠ moved := fun same => no_start s w (eq.trans (congrArg some same))
    simp [endpointHeight, NullarySlide.heights, different]

theorem finish_height (h : ℝ) (w : Fin W) :
    endpointHeight (s.heights h) 1 (d.finish w) = endpointHeight d.vertexHeight 1 (d.finish w) := by
  cases eq : d.finish w with
  | none => simp [endpointHeight]
  | some v =>
    have different : v ≠ moved := fun same => no_finish s w (eq.trans (congrArg some same))
    simp [endpointHeight, NullarySlide.heights, different]

theorem distinct_points {h : ℝ} (within : h ∈ Set.Icc s.bottom s.top) :
    Function.Injective (fun v => (d.vertexX v, s.heights h v)) := by
  intro a b equal
  have hx := congrArg Prod.fst equal
  have hy := congrArg Prod.snd equal
  by_cases ha : a = moved
  · subst a
    by_contra different
    have hb : b ≠ moved := Ne.symm different
    have hy' : h = d.vertexHeight b := by simpa [NullarySlide.heights, hb] using hy
    exact s.vertex_clear b hb (hy' ▸ within) hx.symm
  · by_cases hb : b = moved
    · subst b
      have hy' : d.vertexHeight a = h := by simpa [NullarySlide.heights, ha] using hy
      exact False.elim (s.vertex_clear a ha (hy'.symm ▸ within) hx)
    · apply d.vertex_separation
      exact Prod.ext hx (by simpa [NullarySlide.heights, ha, hb] using hy)

theorem frame_conditions (h : ℝ) (within : h ∈ Set.Icc s.bottom s.top) : s.FrameConditions h where
  inside v := by
    by_cases eq : v = moved
    · simpa only [NullarySlide.heights, eq, ite_true] using
        (show h ∈ Set.Ioo 0 1 from ⟨s.bottom_pos.trans_le within.1, within.2.trans_lt s.top_lt_one⟩)
    · simpa only [NullarySlide.heights, eq, ite_false] using (d.vertex_inside v).2
  injective_points := distinct_points s within
  start_height := start_height s h
  finish_height := finish_height s h
  avoids w v active := by
    by_cases eq : v = moved
    · subst v
      have cover : d.covers w h := by
        apply Set.Ioo_subset_Icc_self
        simpa [Diagram.crosses, NullarySlide.heights] using active
      simpa [NullarySlide.heights] using s.wire_clear w h within cover
    · simpa only [Diagram.x, NullarySlide.heights, eq, ite_false] using
        d.avoids_vertex w v (by
          simpa only [Diagram.crosses, Diagram.lower, Diagram.upper, NullarySlide.heights, eq, ite_false] using active)

def atHeight (h : ℝ) (within : h ∈ Set.Icc s.bottom s.top) : Diagram S V W .point :=
  s.assemble h (frame_conditions s h within)

def frame (t : NullarySlide.Time) : Diagram S V W .point :=
  atHeight s (s.heightAt t) (height_mem s t)

theorem ordered_cut_iff {h : ℝ} (within : h ∈ Set.Icc s.bottom s.top) {y : ℝ} {ws : List (Fin W)} :
    (atHeight s h within).OrderedCut y ws ↔ d.OrderedCut y ws := by
  have same w : (atHeight s h within).crosses w y = d.crosses w y := by
    simp only [Diagram.crosses, Diagram.lower, Diagram.upper, atHeight, NullarySlide.assemble, start_height s, finish_height s]
  constructor <;> intro cut
  · exact ⟨fun w => same w ▸ cut.exact_wires w, cut.ordered⟩
  · exact ⟨fun w => (same w).symm ▸ cut.exact_wires w, cut.ordered⟩

theorem continuous_vertex (v : Fin V) :
    Continuous (fun t : NullarySlide.Time => ((frame s t).vertexX v, (frame s t).vertexHeight v)) := by
  apply continuous_const.prodMk
  by_cases eq : v = moved
  · simpa only [frame, atHeight, NullarySlide.assemble, NullarySlide.heights, eq, ite_true, NullarySlide.heightAt] using
      (show Continuous (fun t : NullarySlide.Time => (1 - t.val) * s.bottom + t.val * s.top) by fun_prop)
  · simp only [frame, atHeight, NullarySlide.assemble, NullarySlide.heights, eq, ite_false]
    exact continuous_const

theorem continuous_wire (w : Fin W) :
    Continuous (fun p : NullarySlide.Time × Set.Icc (d.lower w) (d.upper w) =>
      ((frame s p.1).wire w).point p.2.val) := by
  have wireContinuous : Continuous (fun y : Set.Icc (d.lower w) (d.upper w) =>
      ((d.wire w).x y.val, y.val)) :=
    (continuousOn_iff_continuous_domRestrict.mp (d.wire w).continuous).prodMk continuous_subtype_val
  exact wireContinuous.comp continuous_snd

theorem frame_start : frame s ⟨0, le_rfl, zero_le_one⟩ = atHeight s s.bottom ⟨le_rfl, s.ordered.le⟩ := by
  simp [frame, NullarySlide.heightAt]

theorem frame_finish : frame s ⟨1, zero_le_one, le_rfl⟩ = atHeight s s.top ⟨s.ordered.le, le_rfl⟩ := by
  simp [frame, NullarySlide.heightAt]

theorem height_strict : StrictMono s.heightAt := by
  intro a b less
  have delta := mul_pos (sub_pos.mpr (show a.val < b.val from less)) (sub_pos.mpr s.ordered)
  unfold NullarySlide.heightAt
  nlinarith only [delta]

theorem hits {h : ℝ} (within : h ∈ Set.Icc s.bottom s.top) : ∃ t : NullarySlide.Time, s.heightAt t = h := by
  have pos := sub_pos.mpr s.ordered
  refine ⟨⟨(h - s.bottom) / (s.top - s.bottom), div_nonneg (sub_nonneg.mpr within.1) pos.le,
      (div_le_one pos).mpr (sub_le_sub_right within.2 _)⟩, ?_⟩
  simp only [NullarySlide.heightAt]
  field_simp
  ring

theorem isolated_crossing {other : Fin V} {lo hi : ℝ}
    (horizontal : d.vertexX moved < d.vertexX other)
    (crosses : d.vertexHeight other ∈ Set.Ioo s.bottom s.top)
    (lo_inside : 0 < lo) (lo_bottom : lo < s.bottom)
    (top_hi : s.top < hi) (hi_inside : hi < 1)
    (only : ∀ v, d.vertexHeight v ∈ Set.Icc lo hi → v = moved ∨ v = other) :
    ∃! t : NullarySlide.Time, (frame s t).IsolatesPair moved other lo hi := by
  have different : other ≠ moved := fun eq => (ne_of_lt horizontal) (congrArg d.vertexX eq.symm)
  obtain ⟨t, ht⟩ := hits s (Set.Ioo_subset_Icc_self crosses)
  have atMoved (u : NullarySlide.Time) : (frame s u).vertexHeight moved = s.heightAt u := by
    simp [frame, atHeight, NullarySlide.assemble, NullarySlide.heights]
  have atOther (u : NullarySlide.Time) : (frame s u).vertexHeight other = d.vertexHeight other := by
    simp [frame, atHeight, NullarySlide.assemble, NullarySlide.heights, different]
  refine ⟨t, ?_, ?_⟩
  · refine ⟨?_, horizontal, lo_inside, ?_, ?_, hi_inside, ?_⟩
    · rw [atMoved, atOther, ht]
    · rw [atMoved, ht]
      exact lo_bottom.trans crosses.1
    · rw [atMoved, ht]
      exact crosses.2.trans top_hi
    · intro v inSlab
      by_cases eq : v = moved
      · exact Or.inl eq
      · apply only
        simpa only [frame, atHeight, NullarySlide.assemble, NullarySlide.heights, eq, ite_false] using inSlab
  · intro u hu
    apply (height_strict s).injective
    rw [ht, ← atOther u, hu.same_height, atMoved]

end Silmaril.RuntimeWires.Proofs.ProgressiveNullarySlide
