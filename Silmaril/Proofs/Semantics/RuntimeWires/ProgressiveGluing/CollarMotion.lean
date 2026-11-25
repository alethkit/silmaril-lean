module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarMotionDefs
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarGeometry
public import Mathlib.Data.Finset.Union
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph PolygonalCollar

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {W : ℕ} {cap : CollarSpec O W}
variable (p q : PolygonalCollar cap)

noncomputable def breaks (w : Wire 0 1) : Finset ℝ := Classical.choose w.polygonal

theorem divides_breaks (w : Wire 0 1) : Subdivides w (breaks w) :=
  Classical.choose_spec w.polygonal

/-- A single finite refinement for every strand in both collars. -/
noncomputable def commonHeights : Finset ℝ := by
  classical
  exact {0, 1} ∪ (Finset.univ.biUnion (fun w : Fin W => breaks (p.wire w) ∪ breaks (q.wire w))).filter
    (fun y => y ∈ Set.Icc (0 : ℝ) 1)

theorem divides_common (w : Fin W) :
    Subdivides (p.wire w) (commonHeights p q) ∧ Subdivides (q.wire w) (commonHeights p q) := by
  classical
  have admit_height (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
      {k : ℝ} (h : k ∈ Set.Ioo a b) (pick : k ∈ breaks (p.wire w) ∪ breaks (q.wire w)) :
      k ∈ commonHeights p q := by
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _, pick⟩,
      ⟨ha.1.trans h.1.le, h.2.le.trans hb.2⟩⟩
  refine ⟨?_, ?_⟩ <;> intro a ha b hb hab clear
  · exact divides_breaks _ a ha b hb hab
      (fun k hk he => clear k (admit_height a b ha hb he (Finset.mem_union_left _ hk)) he)
  · exact divides_breaks _ a ha b hb hab
      (fun k hk he => clear k (admit_height a b ha hb he (Finset.mem_union_right _ hk)) he)

theorem interpolate_id (x t : ℝ) : interpolate x x t = x := by unfold interpolate; ring

theorem interpolate_at_zero (a b : ℝ) : interpolate a b 0 = a := by norm_num [interpolate]
theorem interpolate_at_one (a b : ℝ) : interpolate a b 1 = b := by norm_num [interpolate]

theorem interpolate_piece (t : Time) (w : Fin W) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a < b)
    (clear : ∀ k ∈ commonHeights p q, k ∉ Set.Ioo a b) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    interpolate ((p.wire w).x ((1 - s) * a + s * b)) ((q.wire w).x ((1 - s) * a + s * b)) t.val =
      (1 - s) * interpolate ((p.wire w).x a) ((q.wire w).x a) t.val +
        s * interpolate ((p.wire w).x b) ((q.wire w).x b) t.val := by
  rw [(divides_common p q w).1 a ha b hb hab clear s hs, (divides_common p q w).2 a ha b hb hab clear s hs]
  unfold interpolate
  ring

noncomputable def blendedWire (t : Time) (w : Fin W) : Wire 0 1 where
  x y := interpolate ((p.wire w).x y) ((q.wire w).x y) t.val
  increasing := by norm_num
  continuous := by
    unfold interpolate
    exact ((p.wire w).continuous.const_mul (1 - t.val)).add ((q.wire w).continuous.const_mul t.val)
  polygonal := ⟨commonHeights p q, interpolate_piece p q t w⟩

noncomputable def blend (t : Time) : PolygonalCollar cap where
  wire := blendedWire p q t
  bottom w := by
    change interpolate ((p.wire w).x 0) ((q.wire w).x 0) t.val = _
    rw [p.bottom, q.bottom, interpolate_id]
  top w := by
    change interpolate ((p.wire w).x 1) ((q.wire w).x 1) t.val = _
    rw [p.top, q.top, interpolate_id]
  inside w y hy := interpolate_inside (p.inside w y hy) (q.inside w y hy) t.property
  ordered a b y hy order :=
    interpolate_lt (p.ordered a b y hy order) (q.ordered a b y hy order) t.property

theorem blend_subdivides (t : Time) (w : Fin W) :
    Subdivides ((blend p q t).wire w) (commonHeights p q) :=
  interpolate_piece p q t w

/-- Endpoint inequalities on a segment imply strict order throughout it. -/
theorem blend_segment_order (t : Time) (i j : Fin W) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a < b)
    (clear : ∀ k ∈ commonHeights p q, k ∉ Set.Ioo a b)
    (left : ((blend p q t).wire i).x a < ((blend p q t).wire j).x a)
    (right : ((blend p q t).wire i).x b < ((blend p q t).wire j).x b)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ((blend p q t).wire i).x ((1 - s) * a + s * b) <
      ((blend p q t).wire j).x ((1 - s) * a + s * b) := by
  rw [blend_subdivides p q t i a ha b hb hab clear s hs,
    blend_subdivides p q t j a ha b hb hab clear s hs]
  exact interpolate_lt left right hs

theorem wire_eq {a b : ℝ} {first last : Wire a b} (h : first.x = last.x) : first = last := by
  cases first
  cases last
  exact Wire.mk.injEq .. ▸ h

theorem collars_eq {p q : PolygonalCollar cap} (h : p.wire = q.wire) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem blend_zero : blend p q ⟨0, le_rfl, zero_le_one⟩ = p := by
  apply collars_eq
  funext w
  apply wire_eq
  funext y
  exact interpolate_at_zero _ _

theorem blend_one : blend p q ⟨1, zero_le_one, le_rfl⟩ = q := by
  apply collars_eq
  funext w
  apply wire_eq
  funext y
  exact interpolate_at_one _ _

theorem drawing_separate (p : PolygonalCollar cap) {i j : Fin W} (ne : i ≠ j)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) : (p.wire i).x y ≠ (p.wire j).x y := by
  rcases lt_or_gt_of_ne (fun h => ne (cap.bottom_injective h)) with h | h
  · exact (p.ordered i j y hy h).ne
  · exact (p.ordered j i y hy h).ne'

noncomputable def polygonalDrawing (p : PolygonalCollar cap) : Diagram S 0 W .point where
  vertexX := Fin.elim0
  vertexHeight := Fin.elim0
  vertex_inside := fun v => v.elim0
  vertex_separation := fun {a} => a.elim0
  generator := Fin.elim0
  label := cap.label
  start := fun _ => none
  finish := fun _ => none
  wire := p.wire
  wire_inside := p.inside
  start_attached _ := fun v => v.elim0
  finish_attached _ := fun v => v.elim0
  separated ne _ h _ := drawing_separate p ne (Set.Ioo_subset_Icc_self h)
  avoids_vertex _ := fun v => v.elim0
  input_boundary_separated ne _ _ := drawing_separate p ne (by norm_num [Set.mem_Icc])
  output_boundary_separated ne _ _ := drawing_separate p ne (by norm_num [Set.mem_Icc])
  input := fun v => v.elim0
  output := fun v => v.elim0
  input_exact := fun v => v.elim0
  output_exact := fun v => v.elim0
  input_types := fun v => v.elim0
  output_types := fun v => v.elim0
  input_order := fun v => v.elim0
  output_order := fun v => v.elim0

theorem continuous_blend (w : Fin W) :
    Continuous (fun z : Time × Set.Icc (0 : ℝ) 1 => ((blend p q z.1).wire w).point z.2.val) := by
  have hl := (p.wire w).continuous.domRestrict
  have hr := (q.wire w).continuous.domRestrict
  change Continuous (fun z : Time × Set.Icc (0 : ℝ) 1 =>
    (interpolate ((p.wire w).x z.2.val) ((q.wire w).x z.2.val) z.1.val, z.2.val))
  exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (hl.comp continuous_snd)).add ((continuous_subtype_val.comp continuous_fst).mul
      (hr.comp continuous_snd))).prodMk (continuous_subtype_val.comp continuous_snd)

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
