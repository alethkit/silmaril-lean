module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.HorizontalPlacement

open ProgressiveGraph

theorem place_strict (s : ActiveStrip) : StrictMono s.place := by
  intro x y less
  cases s <;> simp only [ActiveStrip.place] <;> linarith

theorem place_inside (s : ActiveStrip) {x : ℝ} (h : x ∈ Set.Ioo (0 : ℝ) 1) :
    s.place x ∈ Set.Ioo (0 : ℝ) 1 := by
  cases s <;> simp only [ActiveStrip.place, Set.mem_Ioo] <;>
    constructor <;> linarith [h.1, h.2]

theorem left_before_right {x y : ℝ} (hx : x < 1) (hy : 0 < y) :
    ActiveStrip.left.place x < ActiveStrip.right.place y := by
  unfold ActiveStrip.place
  linarith

theorem different_strips (s : ActiveStrip) {x y : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    s.place x ≠ s.opposite.place y := by
  cases s
  · exact (left_before_right hx.2 hy.1).ne
  · exact (left_before_right hy.2 hx.1).ne'

def placedWire (s : ActiveStrip) {lo hi : ℝ} (w : Wire lo hi) : Wire lo hi where
  x y := s.place (w.x y)
  increasing := w.increasing
  continuous := by
    cases s
    · exact w.continuous.div_const _
    · exact (continuousOn_const.add w.continuous).div_const _
  polygonal := by
    obtain ⟨knots, chord⟩ := w.polygonal
    refine ⟨knots, ?_⟩
    intro a ha b hb ab clear t ht
    rw [chord a ha b hb ab clear t ht]
    cases s <;> simp only [ActiveStrip.place] <;> ring

def straightWire (x : ℝ) : Wire 0 1 where
  x _ := x
  increasing := zero_lt_one
  continuous := continuousOn_const
  polygonal := by
    refine ⟨∅, ?_⟩
    intros
    ring

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}

/-- Keep endpoints together with the dependent wire type when adjoining
the new block of wires. -/
structure LocatedWire (height : Fin V → ℝ) where
  label : O
  start : Option (Fin V)
  finish : Option (Fin V)
  wire : Wire (endpointHeight height 0 start) (endpointHeight height 1 finish)

variable (s : ActiveStrip) (d : ProgressiveGraph.Diagram S V W .point) (idle : FixedCap S)

def placedWires : Fin (W + idle.profile.size) → LocatedWire (O := O) d.vertexHeight :=
  Fin.append
    (fun i => ⟨d.label i, d.start i, d.finish i, placedWire s (d.wire i)⟩)
    (fun j => ⟨idle.profile.label j, none, none, straightWire (s.opposite.place (idle.profile.x j))⟩)

theorem wire_data_active (i : Fin W) :
    placedWires s d idle (Fin.castAdd idle.profile.size i) =
      ⟨d.label i, d.start i, d.finish i, placedWire s (d.wire i)⟩ :=
  Fin.append_left _ _ i

theorem wire_data_idle (j : Fin idle.profile.size) :
    placedWires s d idle (Fin.natAdd W j) =
      ⟨idle.profile.label j, none, none, straightWire (s.opposite.place (idle.profile.x j))⟩ :=
  Fin.append_right _ _ j

theorem wire_x_active (i : Fin W) (y : ℝ) :
    (placedWires s d idle (Fin.castAdd idle.profile.size i)).wire.x y = s.place (d.x i y) :=
  congrArg (fun q => q.wire.x y) (wire_data_active s d idle i)

theorem wire_x_idle (j : Fin idle.profile.size) (y : ℝ) :
    (placedWires s d idle (Fin.natAdd W j)).wire.x y = s.opposite.place (idle.profile.x j) :=
  congrArg (fun q => q.wire.x y) (wire_data_idle s d idle j)

theorem wires_inside (w : Fin (W + idle.profile.size)) (y : ℝ)
    (h : y ∈ Set.Icc (endpointHeight d.vertexHeight 0 (placedWires s d idle w).start)
      (endpointHeight d.vertexHeight 1 (placedWires s d idle w).finish)) :
    (placedWires s d idle w).wire.x y ∈ Set.Ioo (0 : ℝ) 1 := by
  induction w using Fin.addCases with
  | left i =>
    simp only [wire_data_active] at h
    rw [wire_x_active]
    exact place_inside s (d.wire_inside i y h)
  | right j =>
    rw [wire_x_idle]
    exact place_inside s.opposite (idle.inside j)

theorem lower_contact_covered (w : Fin W) (h : d.start w = none) : d.covers w 0 := by
  have eq : d.lower w = 0 := by simp [ProgressiveGraph.Diagram.lower, endpointHeight, h]
  exact ⟨eq.le, eq ▸ (d.wire w).increasing.le⟩

theorem upper_contact_covered (w : Fin W) (h : d.finish w = none) : d.covers w 1 := by
  have eq : d.upper w = 1 := by simp [ProgressiveGraph.Diagram.upper, endpointHeight, h]
  exact ⟨eq ▸ (d.wire w).increasing.le, eq.ge⟩

/-- Compare the two horizontal positions when the active positions are
known to be covered. The caller supplies separation in the active block. -/
theorem separated_at {w z : Fin (W + idle.profile.size)} (ne : w ≠ z) (y : ℝ)
    (hw : ∀ i, Fin.castAdd idle.profile.size i = w → d.covers i y)
    (hz : ∀ j, Fin.castAdd idle.profile.size j = z → d.covers j y)
    (within : ∀ i j, Fin.castAdd idle.profile.size i = w → Fin.castAdd idle.profile.size j = z →
      i ≠ j → d.x i y ≠ d.x j y) :
    (placedWires s d idle w).wire.x y ≠ (placedWires s d idle z).wire.x y := by
  induction w using Fin.addCases with
  | left i =>
    induction z using Fin.addCases with
    | left j =>
      simp only [wire_x_active]
      exact (place_strict s).injective.ne (within i j rfl rfl (fun e => ne (congrArg _ e)))
    | right j =>
      simp only [wire_x_active, wire_x_idle]
      exact different_strips s (d.wire_inside i y (hw i rfl)) (idle.inside j)
  | right i =>
    induction z using Fin.addCases with
    | left j =>
      simp only [wire_x_active, wire_x_idle]
      exact (different_strips s (d.wire_inside j y (hz j rfl)) (idle.inside i)).symm
    | right j =>
      simp only [wire_x_idle]
      exact (place_strict s.opposite).injective.ne
        (idle.profile.ordered.injective.ne (fun e => ne (congrArg _ e)))

theorem attached (endpoint : Fin W → Option (Fin V))
    (select : LocatedWire (O := O) d.vertexHeight → Option (Fin V))
    (left_eq : ∀ i, select (placedWires s d idle (Fin.castAdd idle.profile.size i)) = endpoint i)
    (right_eq : ∀ i, select (placedWires s d idle (Fin.natAdd W i)) = none)
    (original : ∀ w j, endpoint w = some j → d.x w (d.vertexHeight j) = d.vertexX j)
    (w : Fin (W + idle.profile.size)) (j : Fin V)
    (h : select (placedWires s d idle w) = some j) :
    (placedWires s d idle w).wire.x (d.vertexHeight j) = s.place (d.vertexX j) := by
  induction w using Fin.addCases with
  | left i =>
    rw [left_eq] at h
    simp only [wire_x_active]
    exact congrArg s.place (original i j h)
  | right i =>
    rw [right_eq] at h
    cases h

theorem port_types {n : ℕ} (port : Fin n → Fin W) (word : List O)
    (h : (List.ofFn port).map d.label = word) :
    (List.ofFn (fun i => Fin.castAdd idle.profile.size (port i))).map
      (fun w => (placedWires s d idle w).label) = word := by
  simpa only [List.map_ofFn, Function.comp_def, wire_data_active] using h

def drawing : ProgressiveGraph.Diagram S V (W + idle.profile.size) .point where
  vertexX j := s.place (d.vertexX j)
  vertexHeight := d.vertexHeight
  vertex_inside j := ⟨place_inside s (d.vertex_inside j).1, (d.vertex_inside j).2⟩
  vertex_separation := by
    intro i j eq
    apply d.vertex_separation
    have sameHeight : d.vertexHeight i = d.vertexHeight j := congrArg Prod.snd eq
    exact Prod.ext ((place_strict s).injective (congrArg Prod.fst eq)) sameHeight
  generator := d.generator
  label w := (placedWires s d idle w).label
  start w := (placedWires s d idle w).start
  finish w := (placedWires s d idle w).finish
  wire w := (placedWires s d idle w).wire
  wire_inside := wires_inside s d idle
  start_attached := attached s d idle d.start LocatedWire.start
    (fun i => by simp [wire_data_active]) (fun i => by simp [wire_data_idle]) d.start_attached
  finish_attached := attached s d idle d.finish LocatedWire.finish
    (fun i => by simp [wire_data_active]) (fun i => by simp [wire_data_idle]) d.finish_attached
  separated {w z} ne {y} h k := by
    refine separated_at s d idle (w := w) (z := z) ne y (fun i eq => ?_) (fun j eq => ?_) (fun i j ei ej ij => ?_)
    · subst_vars
      simpa only [ProgressiveGraph.Diagram.covers, ProgressiveGraph.Diagram.lower,
        ProgressiveGraph.Diagram.upper, wire_data_active] using Set.Ioo_subset_Icc_self h
    · subst_vars
      simpa only [ProgressiveGraph.Diagram.covers, ProgressiveGraph.Diagram.lower,
        ProgressiveGraph.Diagram.upper, wire_data_active] using k
    · subst_vars
      exact d.separated ij (by simpa only [wire_data_active] using h)
        (by simpa only [wire_data_active] using k)
  avoids_vertex w j h := by
    induction w using Fin.addCases with
    | left i =>
      simp only [wire_data_active] at h
      rw [wire_x_active]
      exact (place_strict s).injective.ne (d.avoids_vertex i j h)
    | right i =>
      rw [wire_x_idle]
      exact (different_strips s (d.vertex_inside j).1 (idle.inside i)).symm
  input_boundary_separated ne h k := by
    refine separated_at s d idle ne 0 (fun i eq => ?_) (fun j eq => ?_) (fun i j ei ej ij => ?_)
    · subst_vars
      exact lower_contact_covered d i (by simpa [wire_data_active, wire_data_idle] using h)
    · subst_vars
      exact lower_contact_covered d j (by simpa [wire_data_active, wire_data_idle] using k)
    · subst_vars
      exact d.input_boundary_separated ij (by simpa [wire_data_active, wire_data_idle] using h) (by simpa [wire_data_active, wire_data_idle] using k)
  output_boundary_separated ne h k := by
    refine separated_at s d idle ne 1 (fun i eq => ?_) (fun j eq => ?_) (fun i j ei ej ij => ?_)
    · subst_vars
      exact upper_contact_covered d i (by simpa [wire_data_active, wire_data_idle] using h)
    · subst_vars
      exact upper_contact_covered d j (by simpa [wire_data_active, wire_data_idle] using k)
    · subst_vars
      exact d.output_boundary_separated ij (by simpa [wire_data_active, wire_data_idle] using h) (by simpa [wire_data_active, wire_data_idle] using k)
  input j i := Fin.castAdd idle.profile.size (d.input j i)
  output j i := Fin.castAdd idle.profile.size (d.output j i)
  input_exact j w := by
    induction w using Fin.addCases with
    | left i => simpa only [wire_data_active, Fin.castAdd_inj] using d.input_exact j i
    | right i =>
      simp only [wire_data_idle, reduceCtorEq, false_iff, not_exists]
      intro k eq
      have same := congrArg Fin.val eq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at same
      omega
  output_exact j w := by
    induction w using Fin.addCases with
    | left i => simpa only [wire_data_active, Fin.castAdd_inj] using d.output_exact j i
    | right i =>
      simp only [wire_data_idle, reduceCtorEq, false_iff, not_exists]
      intro k eq
      have same := congrArg Fin.val eq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at same
      omega
  input_types j := port_types s d idle _ _ (d.input_types j)
  output_types j := port_types s d idle _ _ (d.output_types j)
  input_order j {i k} ij {y} a b above := by
    simp only [wire_data_active] at a b
    simp only [wire_x_active]
    exact place_strict s (d.input_order j (i := i) (j := k) ij (h := y) a b above)
  output_order j {i k} ij {y} below a b := by
    simp only [wire_data_active] at a b
    simp only [wire_x_active]
    exact place_strict s (d.output_order j (i := i) (j := k) ij (h := y) below a b)

end Silmaril.RuntimeWires.Proofs.HorizontalPlacement
