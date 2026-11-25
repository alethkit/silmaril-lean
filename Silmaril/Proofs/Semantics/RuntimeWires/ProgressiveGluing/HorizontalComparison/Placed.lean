module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Compression
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Comparison
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Drawing
import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.HorizontalComparison

open ProgressiveGraph
open HorizontalPlacement (drawing placedWires LocatedWire wire_data_active wire_data_idle)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W V' W' : ℕ}
variable {d : ProgressiveGraph.Diagram S V W .point} {e : ProgressiveGraph.Diagram S V' W' .point}

def renamedWires (h : d.IncidenceEquiv e) (I : ℕ) : Fin (W + I) ≃ Fin (W' + I) :=
  finSumFinEquiv.symm.trans ((h.wire.sumCongr (Equiv.refl (Fin I))).trans finSumFinEquiv)

theorem wire_active (h : d.IncidenceEquiv e) (I : ℕ) (i : Fin W) :
    renamedWires h I (Fin.castAdd I i) = Fin.castAdd I (h.wire i) := by
  simp only [renamedWires, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]

theorem wire_idle (h : d.IncidenceEquiv e) (I : ℕ) (j : Fin I) :
    renamedWires h I (Fin.natAdd W j) = Fin.natAdd W' j := by
  simp only [renamedWires, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_right]

variable (s : ActiveStrip) (idle : FixedCap S)

theorem drawing_inputs (d : ProgressiveGraph.Diagram S V W .point) (j : Fin V) :
    (drawing s d idle).inputs j = (d.inputs j).map (Fin.castAdd idle.profile.size) := by
  rw [ProgressiveGraph.Diagram.inputs, ProgressiveGraph.Diagram.inputs, List.map_ofFn]
  rfl

theorem drawing_outputs (d : ProgressiveGraph.Diagram S V W .point) (j : Fin V) :
    (drawing s d idle).outputs j = (d.outputs j).map (Fin.castAdd idle.profile.size) := by
  rw [ProgressiveGraph.Diagram.outputs, ProgressiveGraph.Diagram.outputs, List.map_ofFn]
  rfl

theorem label_placed (h : d.IncidenceEquiv e) (w : Fin (W + idle.profile.size)) :
    (drawing s e idle).label (renamedWires h idle.profile.size w) = (drawing s d idle).label w := by
  change (placedWires s e idle (renamedWires h idle.profile.size w)).label = (placedWires s d idle w).label
  induction w using Fin.addCases with
  | left i => rw [wire_active, wire_data_active, wire_data_active, h.label]
  | right j => rw [wire_idle, wire_data_idle, wire_data_idle]

theorem ports_placed (h : d.IncidenceEquiv e) (xs : List (Fin W)) :
    (xs.map h.wire).map (Fin.castAdd idle.profile.size) =
      (xs.map (Fin.castAdd idle.profile.size)).map (renamedWires h idle.profile.size) := by
  rw [List.map_map, List.map_map]
  exact congrArg (fun f => xs.map f) (funext fun i => (wire_active h idle.profile.size i).symm)

def placedIncidence (h : d.IncidenceEquiv e) : (drawing s d idle).IncidenceEquiv (drawing s e idle) where
  vertex := h.vertex
  wire := renamedWires h idle.profile.size
  generator := h.generator
  label := label_placed s idle h
  inputs j := by
    rw [drawing_inputs, drawing_inputs, h.inputs]
    exact ports_placed idle h _
  outputs j := by
    rw [drawing_outputs, drawing_outputs, h.outputs]
    exact ports_placed idle h _

def pointPlacement (s : ActiveStrip) (z : ℝ × ℝ) : ℝ × ℝ := (s.place z.1, z.2)

theorem trace_active (d : ProgressiveGraph.Diagram S V W .point) (i : Fin W) :
    ((drawing s d idle).wire (Fin.castAdd idle.profile.size i)).trace =
      pointPlacement s '' (d.wire i).trace := by
  have eq := congrArg (fun w : LocatedWire (O := O) d.vertexHeight => w.wire.trace)
    (wire_data_active s d idle i)
  exact eq.trans (Set.image_image (pointPlacement s) (d.wire i).point
    (Set.Icc (d.lower i) (d.upper i))).symm

def idlePoint (i : Fin idle.profile.size) (y : ℝ) : ℝ × ℝ :=
  (s.opposite.place (idle.profile.x i), y)

theorem trace_idle (d : ProgressiveGraph.Diagram S V W .point) (i : Fin idle.profile.size) :
    ((drawing s d idle).wire (Fin.natAdd W i)).trace =
      idlePoint s idle i '' Set.Icc (0 : ℝ) 1 :=
  congrArg (fun w : LocatedWire (O := O) d.vertexHeight => w.wire.trace) (wire_data_idle s d idle i)

theorem height_image_unit (f : CapHomeomorph) : f.height '' Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
  have lo := height_fixed f (.inl (le_rfl : (0 : ℝ) ≤ 0))
  have hi := height_fixed f (.inr (le_rfl : (1 : ℝ) ≤ 1))
  ext y
  obtain ⟨x, rfl⟩ := f.height.surjective y
  rw [f.height.injective.mem_set_image]
  calc
    x ∈ Set.Icc (0 : ℝ) 1 ↔ f.height x ∈ Set.Icc (f.height 0) (f.height 1) := by
      simp only [Set.mem_Icc, f.increasing.le_iff_le]
    _ ↔ f.height x ∈ Set.Icc 0 1 := by rw [lo, hi]

variable (h : d.CapComparison e)
variable {span : InteriorRange} (c : Compression h.map s span)
variable (source : drawnXs d ⊆ Set.Icc span.left span.right)
variable (target : drawnXs e ⊆ Set.Icc span.left span.right)

include source target in
theorem placed_active_point (w : Fin W) {y : ℝ} (cover : d.covers w y) :
    c.ambient.plane (s.place (d.x w y), y) = pointPlacement s (h.map.plane (d.x w y, y)) := by
  have move := CapClasses.compare_point h w cover
  have after : fibre h.map y (d.x w y) ∈ Set.Icc span.left span.right := by
    have eq : fibre h.map y (d.x w y) = e.x (h.incidence.wire w) (h.map.height y) :=
      congrArg Prod.fst move.2
    rw [eq]
    exact target (wire_in_drawnXs e _ move.1)
  rw [c.ambient_active (source (wire_in_drawnXs d w cover)) after, plane_eq]
  rfl

include source target in
theorem placed_trace_active (w : Fin W) :
    c.ambient.plane '' ((drawing s d idle).wire (Fin.castAdd idle.profile.size w)).trace =
      ((drawing s e idle).wire (Fin.castAdd idle.profile.size (h.incidence.wire w))).trace := by
  rw [trace_active, trace_active, Set.image_image, ← h.trace w, Set.image_image]
  apply Set.image_congr
  rintro _ ⟨y, cover, rfl⟩
  exact placed_active_point s h c source target w cover

theorem placed_trace_idle (i : Fin idle.profile.size) :
    c.ambient.plane '' ((drawing s d idle).wire (Fin.natAdd W i)).trace =
      ((drawing s e idle).wire (Fin.natAdd W' i)).trace := by
  rw [trace_idle, trace_idle, Set.image_image]
  have eq : (c.ambient.plane ∘ idlePoint s idle i) = (idlePoint s idle i ∘ h.map.height) :=
    funext fun y => c.ambient_idle (idle.inside i) y
  change (c.ambient.plane ∘ idlePoint s idle i) '' Set.Icc (0 : ℝ) 1 = _
  rw [eq]
  change (fun y => idlePoint s idle i (h.map.height y)) '' Set.Icc (0 : ℝ) 1 = _
  rw [← Set.image_image, height_image_unit]

include source target in
theorem placed_trace (w : Fin (W + idle.profile.size)) :
    c.ambient.plane '' ((drawing s d idle).wire w).trace =
      ((drawing s e idle).wire (renamedWires h.incidence idle.profile.size w)).trace := by
  induction w using Fin.addCases with
  | left i =>
    rw [wire_active]
    exact placed_trace_active s idle h c source target i
  | right j =>
    rw [wire_idle]
    exact placed_trace_idle s idle h c j

include source target in
theorem placed_vertex (j : Fin V) :
    c.ambient.plane ((drawing s d idle).vertexX j, (drawing s d idle).vertexHeight j) =
      ((drawing s e idle).vertexX (h.incidence.vertex j),
        (drawing s e idle).vertexHeight (h.incidence.vertex j)) := by
  have eq : fibre h.map (d.vertexHeight j) (d.vertexX j) = e.vertexX (h.incidence.vertex j) :=
    congrArg Prod.fst (h.vertex j)
  have eqY : h.map.height (d.vertexHeight j) = e.vertexHeight (h.incidence.vertex j) :=
    (h.map.height_eq _).symm.trans (congrArg Prod.snd (h.vertex j))
  have after : fibre h.map (d.vertexHeight j) (d.vertexX j) ∈ Set.Icc span.left span.right := by
    rw [eq]
    exact target (vertex_in_drawnXs e _)
  change c.ambient.plane (s.place (d.vertexX j), d.vertexHeight j) =
    (s.place (e.vertexX (h.incidence.vertex j)), e.vertexHeight (h.incidence.vertex j))
  rw [c.ambient_active (source (vertex_in_drawnXs d j)) after, eq, eqY]

def placedComparison : (drawing s d idle).CapComparison (drawing s e idle) :=
  let span := Classical.choose (common_range d e)
  let bounds := Classical.choose_spec (common_range d e)
  let c := compression h.map s span
  { map := c.ambient
    incidence := placedIncidence s idle h.incidence
    trace := placed_trace s idle h c bounds.1 bounds.2
    vertex := placed_vertex s idle h c bounds.1 bounds.2 }

end Silmaril.RuntimeWires.Proofs.HorizontalComparison
