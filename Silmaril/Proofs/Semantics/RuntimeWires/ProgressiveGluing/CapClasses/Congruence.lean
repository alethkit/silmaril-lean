module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.GluedIds
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Vertices

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.CapClasses

open ProgressiveGraph ProgressiveGraph.Diagram.PartialVerticalMatch
open CollarAssociator

universe u v w z
variable {O : Type u} {S : Signature.{u,v} O}
variable {V W V' W' : ℕ}
variable {d : ProgressiveGraph.Diagram S V W .point} {e : ProgressiveGraph.Diagram S V' W' .point}

theorem image_wire_piece {I : Type w} {J : Type z} (h : d.CapComparison e)
    (eqv : I ≃ J) (source : Fin W → I) (target : Fin W' → J)
    (name : ∀ i, target (h.incidence.wire i) = eqv (source i))
    (loc : ℝ → ℝ) (map : ℝ × ℝ → ℝ × ℝ)
    (placed : ∀ i y, d.covers i y → map (d.x i y, loc y) =
      ((h.map.plane (d.x i y, y)).1, loc (h.map.plane (d.x i y, y)).2))
    (w : I) :
    map '' {z | wirePiece d source loc w z} = {z | wirePiece e target loc (eqv w) z} := by
  ext z
  constructor
  · rintro ⟨_, ⟨i, y, id, cover, rfl⟩, point⟩
    have moved := compare_point h i cover
    refine ⟨h.incidence.wire i, h.map.height y, (name i).trans (congrArg eqv id), moved.1, ?_⟩
    rw [placed i y cover, moved.2] at point
    exact point
  · rintro ⟨j, y, id, cover, rfl⟩
    obtain ⟨i, rfl⟩ := h.incidence.wire.surjective j
    have mem : (e.x (h.incidence.wire i) y, y) ∈ (e.wire (h.incidence.wire i)).trace := ⟨y, cover, rfl⟩
    rw [← h.trace i] at mem
    obtain ⟨_, ⟨s, inTrace, rfl⟩, point⟩ := mem
    refine ⟨(d.x i s, loc s), ⟨i, s, eqv.injective ((name i).symm.trans id), inTrace, rfl⟩, ?_⟩
    rw [placed i s inTrace]
    change h.map.plane (d.x i s, s) = _ at point
    rw [point]

theorem trace_parts {d : ProgressiveGraph.Diagram S V W .point} {e : ProgressiveGraph.Diagram S V' W' .point}
    (m : d.OrderedVerticalMatch e) (w : Fin (wireCount m.lowerJoin.glue e)) :
    (m.glue.wire w).trace =
      {p | wirePiece d (leftWire m) Height.lower w p} ∪
        ({p | collarPiece m (fun a => leftWire m a.val) Height.collar w p} ∪
          {p | wirePiece e (rightWire m) Height.upper w p}) := by
  ext z
  exact (trace_mem m.glue w z).trans (collared_expand m id id w z)

variable {a b c : CapProfile O}
variable {p p' : FixedDrawing S a b} {q q' : FixedDrawing S b c}
variable (h : p.drawing.CapComparison p'.drawing) (k : q.drawing.CapComparison q'.drawing)

theorem collar_named (w : Contact p.drawing) :
    leftWire (matching p' q') (renameOutput h w).val =
      gluedWires h k (leftWire (matching p q) w.val) :=
  (glued_left h k w.val).symm

include k in
theorem collar_point (w : Contact p.drawing) (y : ℝ) :
    interpolate (p'.drawing.x (renameOutput h w).val 1)
      (q'.drawing.x ((matching p' q').contact (renameOutput h w)).val 0) y =
    interpolate (p.drawing.x w.val 1) (q.drawing.x ((matching p q).contact w).val 0) y := by
  rw [contact_transport h k]
  change interpolate (p'.drawing.x (h.incidence.wire w.val) 1)
    (q'.drawing.x (k.incidence.wire ((matching p q).contact w).val) 0) y = _
  rw [output_x h _ w.property, input_x k _ ((matching p q).contact w).property]

theorem image_collar_piece (w : Fin (glue p q).wires) :
    (collared h.map k.map).plane ''
        {z | collarPiece (matching p q) (fun a => leftWire (matching p q) a.val) Height.collar w z} =
      {z | collarPiece (matching p' q') (fun a => leftWire (matching p' q') a.val)
        Height.collar (gluedWires h k w) z} := by
  ext z
  constructor
  · rintro ⟨_, ⟨i, y, name, bounds, rfl⟩, point⟩
    refine ⟨renameOutput h i, y, (collar_named h k i).trans (congrArg (gluedWires h k) name), bounds, ?_⟩
    have fixed := collared_middle h.map k.map
      (interpolate (p.drawing.x i.val 1) (q.drawing.x ((matching p q).contact i).val 0) y, y) bounds
    exact (congrArg (fun x : ℝ => (x, Height.collar y)) (collar_point h k i y)).trans (fixed.symm.trans point)
  · rintro ⟨j, y, name, bounds, rfl⟩
    obtain ⟨i, rfl⟩ := (renameOutput h).surjective j
    have ix : leftWire (matching p q) i.val = w :=
      (gluedWires h k).injective ((collar_named h k i).symm.trans name)
    refine ⟨(interpolate (p.drawing.x i.val 1) (q.drawing.x ((matching p q).contact i).val 0) y,
      Height.collar y), ⟨i, y, ix, bounds, rfl⟩, ?_⟩
    have fixed := collared_middle h.map k.map
      (interpolate (p.drawing.x i.val 1) (q.drawing.x ((matching p q).contact i).val 0) y, y) bounds
    exact fixed.trans (congrArg (fun x : ℝ => (x, Height.collar y)) (collar_point h k i y).symm)

theorem glue_trace (w : Fin (glue p q).wires) :
    (collared h.map k.map).plane '' ((glue p q).drawing.wire w).trace =
      ((glue p' q').drawing.wire (gluedWires h k w)).trace := by
  change (collared h.map k.map).plane '' ((matching p q).glue.wire w).trace =
    ((matching p' q').glue.wire (gluedWires h k w)).trace
  rw [trace_parts (matching p q), trace_parts (matching p' q'), Set.image_union, Set.image_union]
  have l := image_wire_piece h (gluedWires h k) (leftWire (matching p q)) (leftWire (matching p' q'))
    (fun i => (glued_left h k i).symm) Height.lower (collared h.map k.map).plane
    (fun i y cover => collared_lower h.map k.map (p.drawing.x i y, y) (covers_unit p.drawing cover).2) w
  have r := image_wire_piece k (gluedWires h k) (rightWire (matching p q)) (rightWire (matching p' q'))
    (fun i => (glued_right h k i).symm) Height.upper (collared h.map k.map).plane
    (fun i y cover => collared_upper h.map k.map (q.drawing.x i y, y) (covers_unit q.drawing cover).1) w
  rw [l, r, image_collar_piece h k]

theorem glue_vertex (v : Fin (glue p q).vertices) :
    (collared h.map k.map).plane ((glue p q).drawing.vertexX v, (glue p q).drawing.vertexHeight v) =
      ((glue p' q').drawing.vertexX (gluedVertices h k v), (glue p' q').drawing.vertexHeight (gluedVertices h k v)) := by
  change (collared h.map k.map).plane ((matching p q).glue.vertexX v, (matching p q).glue.vertexHeight v) =
    ((matching p' q').glue.vertexX (gluedVertices h k v), (matching p' q').glue.vertexHeight (gluedVertices h k v))
  induction v using Fin.addCases with
  | left i =>
    rw [vertex_left, vertexX_lower, vertexX_lower, height_lower, height_lower]
    rw [collared_lower h.map k.map (p.drawing.vertexX i, p.drawing.vertexHeight i)
      (p.drawing.vertex_inside i).2.2.le, h.vertex]
  | right i =>
    rw [vertex_right, vertexX_upper, vertexX_upper, height_upper, height_upper]
    rw [collared_upper h.map k.map (q.drawing.vertexX i, q.drawing.vertexHeight i)
      (q.drawing.vertex_inside i).2.1.le, k.vertex]

noncomputable def glue_comparison : (glue p q).drawing.CapComparison (glue p' q').drawing where
  map := collared h.map k.map
  incidence := gluedIncidence h k
  trace := glue_trace h k
  vertex := glue_vertex h k

end Silmaril.RuntimeWires.Proofs.CapClasses
