module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Defs
public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Drawing
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepRows
import Mathlib.Data.List.OfFn

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CapWhiskering

open ProgressiveGraph ProgressiveGraph.Diagram
open HorizontalPlacement (place_strict left_before_right)
open Sliced (Row)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : FixedCap S}
variable (side : ActiveStrip) (p : FixedDrawing S a.profile b.profile) (idle : FixedCap S)

local notation "placed" => FixedDrawing.drawing (ActiveStrip.placeDrawing side p idle)

private def activeSlot (z : LayerSlot p.vertices p.wires) :
    LayerSlot (side.placeDrawing p idle).vertices (side.placeDrawing p idle).wires :=
  Sum.map (side.activeWire p idle) (side.vertexIndex p idle) z

private def idleSlot (i : Fin idle.profile.size) :
    LayerSlot (side.placeDrawing p idle).vertices (side.placeDrawing p idle).wires :=
  .inl (side.idleWire p idle i)

private theorem active_coordinate (h : ℝ) (z : LayerSlot p.vertices p.wires) :
    (placed).slotX h (activeSlot side p idle z) = side.place (p.drawing.slotX h z) := by
  cases z with
  | inl w => exact side.active_x p idle w h
  | inr v => rfl

private theorem idle_coordinate (h : ℝ) (i : Fin idle.profile.size) :
    (placed).slotX h (idleSlot side p idle i) = side.opposite.place (idle.profile.x i) :=
  side.idle_x p idle i h

private theorem active_atLayer (h : ℝ) (z : LayerSlot p.vertices p.wires) :
    (placed).atLayer h (activeSlot side p idle z) ↔ p.drawing.atLayer h z := by
  cases z with
  | inl w =>
    have endpoints := side.active_endpoints p idle w
    change (placed).crosses (side.activeWire p idle w) h ↔ p.drawing.crosses w h
    unfold Diagram.crosses Diagram.lower Diagram.upper
    rw [endpoints.1, endpoints.2]
    change h ∈ Set.Ioo (endpointHeight p.drawing.vertexHeight 0 ((p.drawing.start w).map id))
      (endpointHeight p.drawing.vertexHeight 1 ((p.drawing.finish w).map id)) ↔ _
    rw [Option.map_id_apply, Option.map_id_apply]
  | inr v => rfl

private theorem idle_atLayer {h : ℝ} (inside : h ∈ Set.Ioo 0 1) (i : Fin idle.profile.size) :
    (placed).atLayer h (idleSlot side p idle i) := by
  have endpoints := side.idle_endpoints p idle i
  change (placed).crosses (side.idleWire p idle i) h
  unfold Diagram.crosses Diagram.lower Diagram.upper
  rwa [endpoints.1, endpoints.2]

private theorem active_inside {h : ℝ} {z : LayerSlot p.vertices p.wires} (hz : p.drawing.atLayer h z) :
    p.drawing.slotX h z ∈ Set.Ioo 0 1 := by
  cases z with
  | inl w => exact p.drawing.wire_inside w h (Set.Ioo_subset_Icc_self (show p.drawing.crosses w h from hz))
  | inr v => exact (p.drawing.vertex_inside v).1

private theorem slots_exhaustive
    (z : LayerSlot (side.placeDrawing p idle).vertices (side.placeDrawing p idle).wires) :
    (∃ c, activeSlot side p idle c = z) ∨ (∃ i, idleSlot side p idle i = z) := by
  cases z with
  | inl w =>
    change Fin (p.wires + idle.profile.size) at w
    induction w using Fin.addCases with
    | left j => exact Or.inl ⟨.inl j, rfl⟩
    | right j => exact Or.inr ⟨j, rfl⟩
  | inr j =>
    exact Or.inl ⟨.inr ((side.vertexIndex p idle).symm j),
      congrArg Sum.inr ((side.vertexIndex p idle).apply_symm_apply j)⟩

/-- The slots at an event are the transported active slots and the whole
idle block in their horizontal order. The cuts delimiting the two layers
are independent. -/
private theorem slots {h lo hi lo' hi' : ℝ}
    (s : p.drawing.LayerSlice h lo hi) (t : (placed).LayerSlice h lo' hi') :
    t.slots = match side with
      | .left => s.slots.map (activeSlot side p idle) ++ List.ofFn (idleSlot side p idle)
      | .right => List.ofFn (idleSlot side p idle) ++ s.slots.map (activeSlot side p idle) := by
  let active := s.slots.map (activeSlot side p idle)
  let passive := List.ofFn (idleSlot side p idle)
  let x := (placed).slotX h
  have orderedActive : active.Pairwise (fun i j => x i < x j) :=
    List.pairwise_map.mpr (s.ordered.imp fun lt => by
      dsimp [x]
      rw [active_coordinate, active_coordinate]
      exact place_strict side lt)
  have orderedPassive : passive.Pairwise (fun i j => x i < x j) :=
    List.pairwise_ofFn.mpr (fun i j lt => by
      dsimp [x]
      rw [idle_coordinate, idle_coordinate]
      exact place_strict side.opposite (idle.profile.ordered lt))
  have ordered : (match side with | .left => active ++ passive | .right => passive ++ active).Pairwise
      (fun i j => x i < x j) := by
    cases side
    · refine List.pairwise_append.mpr ⟨orderedActive, orderedPassive, ?_⟩
      intro i hi j hj
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hi
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hj
      dsimp [x]
      rw [active_coordinate, idle_coordinate]
      exact left_before_right
        (active_inside p ((s.exact_slots c).mp hc)).2 (idle.inside slot).1
    · refine List.pairwise_append.mpr ⟨orderedPassive, orderedActive, ?_⟩
      intro i hi j hj
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hj
      dsimp [x]
      rw [idle_coordinate, active_coordinate]
      exact left_before_right
        (idle.inside slot).2 (active_inside p ((s.exact_slots c).mp hc)).1
  have inside : h ∈ Set.Ioo 0 1 :=
    ⟨s.isolation.lo_inside.trans s.isolation.below, s.isolation.above.trans s.isolation.hi_inside⟩
  have members (z) : (placed).atLayer h z ↔ z ∈ active ∨ z ∈ passive := by
    constructor
    · intro hz
      rcases slots_exhaustive side p idle z with ⟨c, rfl⟩ | ⟨j, rfl⟩
      · exact .inl (List.mem_map.mpr
          ⟨c, (s.exact_slots c).mpr ((active_atLayer side p idle h c).mp hz), rfl⟩)
      · exact .inr (List.mem_ofFn.mpr ⟨j, rfl⟩)
    · rintro (ha | hp)
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
        exact (active_atLayer side p idle h c).mpr ((s.exact_slots c).mp hc)
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
        exact idle_atLayer side p idle inside j
  have same (z) : z ∈ t.slots ↔ z ∈
      (match side with | .left => active ++ passive | .right => passive ++ active) := by
    rw [t.exact_slots, members]
    cases side <;> simp only [List.mem_append, or_comm]
  have nodup (l : List _) (hl : l.Pairwise (fun i j => x i < x j)) : l.Nodup :=
    hl.imp (fun lt => ne_of_apply_ne x (ne_of_lt lt))
  have perm := (List.perm_ext_iff_of_nodup (nodup _ t.ordered) (nodup _ ordered)).mpr same
  have ids := perm.eq_of_pairwise (fun _ _ _ _ h k => (lt_asymm h k).elim) t.ordered ordered
  cases side <;> exact ids

private theorem layer_cells {V W : ℕ} (e : ProgressiveGraph.Diagram S V W .point)
    (l : List (LayerSlot V W)) :
    (e.layerRow l).cells = l.map (Sum.map e.label e.generator) := by
  induction l with
  | nil => exact Row.cells_straight []
  | cons z tail ih =>
    cases z with
    | inl w =>
      change (Row.wire (e.label w) (e.layerRow tail)).cells = _
      rw [show (Row.wire (e.label w) (e.layerRow tail)).cells =
          .inl (e.label w) :: (e.layerRow tail).cells from Row.cells_pass [e.label w] _,
        ih]
      rfl
    | inr v =>
      change (Row.box (e.generator v) (e.layerRow tail)).cells = _
      rw [Row.cells_box, ih]
      rfl

theorem levels : (placed).levels = p.drawing.levels := by rfl

theorem level_count : (placed).levelCount = p.drawing.levelCount :=
  congrArg List.length (levels side p idle)

/-- Whiskering fixes the level indices, including ties, and adds only
passive wire cells at one end of each independently read row. -/
theorem row_cells (s : p.drawing.LayerSweep) (t : (placed).LayerSweep) (i : Fin p.drawing.levelCount) :
    (t.row (i.cast (level_count side p idle).symm)).cells = match side with
      | .left => (s.row i).cells ++ idle.types.map Sum.inl
      | .right => idle.types.map Sum.inl ++ (s.row i).cells := by
  rw [ProgressiveGluing.sweep_row_cells, ProgressiveGluing.sweep_row_cells,
    slots side p idle (s.layer i) (t.layer (i.cast (level_count side p idle).symm)),
    layer_cells, layer_cells]
  have active : ((s.layer i).slots.map (activeSlot side p idle)).map (Sum.map (placed).label (placed).generator) =
      (s.layer i).slots.map (Sum.map p.drawing.label p.drawing.generator) := by
    rw [List.map_map]
    congr 1
    funext z
    cases z with
    | inl w => exact congrArg Sum.inl (side.active_label p idle w)
    | inr v => rfl
  have passive : (List.ofFn (idleSlot side p idle)).map (Sum.map (placed).label (placed).generator) =
      idle.types.map Sum.inl := by
    rw [List.map_ofFn, FixedCap.types, List.map_ofFn]
    exact congrArg List.ofFn (funext fun j => congrArg Sum.inl (side.idle_label p idle j))
  cases side <;> simp only [List.map_append, active, passive]

end Silmaril.RuntimeWires.Proofs.CapWhiskering
