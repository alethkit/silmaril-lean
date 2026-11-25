module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Matching
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Incidence
import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.CapClasses

open ProgressiveGraph ProgressiveGraph.Diagram.PartialVerticalMatch
open CollarAssociator (leftWire rightWire descend descend_left descend_right wire_cases wire_contact
  left_label right_label generator_lower generator_upper inputs_lower inputs_upper outputs_lower outputs_upper)

universe u v
variable {O : Type u} {S : Signature.{u,v} O}
variable {a b c : CapProfile O}
variable {p p' : FixedDrawing S a b} {q q' : FixedDrawing S b c}
variable (h : p.drawing.CapComparison p'.drawing) (k : q.drawing.CapComparison q'.drawing)

noncomputable def wireMap : Fin (glue p q).wires → Fin (glue p' q').wires :=
  descend (matching p q) (leftWire (matching p' q') ∘ h.incidence.wire)
    (rightWire (matching p' q') ∘ k.incidence.wire)

theorem map_left (i : Fin p.wires) :
    wireMap h k (leftWire (matching p q) i) = leftWire (matching p' q') (h.incidence.wire i) :=
  descend_left _ _ _ i

theorem map_right (i : Fin q.wires) :
    wireMap h k (rightWire (matching p q) i) = rightWire (matching p' q') (k.incidence.wire i) := by
  apply descend_right
  intro w
  have glue_eq := wire_contact (matching p' q') (renameOutput h w)
  rw [contact_transport h k] at glue_eq
  exact glue_eq

theorem map_inverse (w : Fin (glue p q).wires) :
    wireMap (compare_symm h) (compare_symm k) (wireMap h k w) = w := by
  rcases wire_cases (matching p q) w with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [map_left, map_left]
    exact congrArg (leftWire (matching p q)) (h.incidence.wire.symm_apply_apply i)
  · rw [map_right, map_right]
    exact congrArg (rightWire (matching p q)) (k.incidence.wire.symm_apply_apply i)

noncomputable def gluedWires : Fin (glue p q).wires ≃ Fin (glue p' q').wires where
  toFun := wireMap h k
  invFun := wireMap (compare_symm h) (compare_symm k)
  left_inv := map_inverse h k
  right_inv w := by
    rcases wire_cases (matching p' q') w with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [map_left, map_left]
      exact congrArg (leftWire (matching p' q')) (h.incidence.wire.apply_symm_apply i)
    · rw [map_right, map_right]
      exact congrArg (rightWire (matching p' q')) (k.incidence.wire.apply_symm_apply i)

theorem glued_left (i : Fin p.wires) :
    gluedWires h k (leftWire (matching p q) i) = leftWire (matching p' q') (h.incidence.wire i) :=
  map_left h k i

theorem glued_right (i : Fin q.wires) :
    gluedWires h k (rightWire (matching p q) i) = rightWire (matching p' q') (k.incidence.wire i) :=
  map_right h k i

def gluedVertices : Fin (p.vertices + q.vertices) ≃ Fin (p'.vertices + q'.vertices) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr h.incidence.vertex k.incidence.vertex).trans finSumFinEquiv)

theorem vertex_left (v : Fin p.vertices) :
    gluedVertices h k (Fin.castAdd q.vertices v) = Fin.castAdd q'.vertices (h.incidence.vertex v) := by
  simp only [gluedVertices, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]

theorem vertex_right (v : Fin q.vertices) :
    gluedVertices h k (Fin.natAdd p.vertices v) = Fin.natAdd p'.vertices (k.incidence.vertex v) := by
  simp only [gluedVertices, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]

theorem glue_generators (v : Fin (glue p q).vertices) :
    (glue p' q').drawing.generator (gluedVertices h k v) = (glue p q).drawing.generator v := by
  change (matching p' q').glue.generator (gluedVertices h k v) = (matching p q).glue.generator v
  induction v using Fin.addCases with
  | left i => rw [vertex_left, generator_lower, generator_lower, h.incidence.generator]
  | right i => rw [vertex_right, generator_upper, generator_upper, k.incidence.generator]

theorem glue_labels (w : Fin (glue p q).wires) :
    (glue p' q').drawing.label (gluedWires h k w) = (glue p q).drawing.label w := by
  change (matching p' q').glue.label (gluedWires h k w) = (matching p q).glue.label w
  rcases wire_cases (matching p q) w with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [glued_left, left_label, left_label, h.incidence.label]
  · rw [glued_right, right_label, right_label, k.incidence.label]

theorem glue_ports
    (ports : ∀ {V W}, ProgressiveGraph.Diagram S V W .point → Fin V → List (Fin W))
    (lo : ∀ {V V' W W'} {l : ProgressiveGraph.Diagram S V W .point}
      {r : ProgressiveGraph.Diagram S V' W' .point} (m : l.OrderedVerticalMatch r) (i : Fin V),
      ports m.glue (Fin.castAdd V' i) = (ports l i).map (leftWire m))
    (hi : ∀ {V V' W W'} {l : ProgressiveGraph.Diagram S V W .point}
      {r : ProgressiveGraph.Diagram S V' W' .point} (m : l.OrderedVerticalMatch r) (i : Fin V'),
      ports m.glue (Fin.natAdd V i) = (ports r i).map (rightWire m))
    (hp : ∀ i, ports p'.drawing (h.incidence.vertex i) = (ports p.drawing i).map h.incidence.wire)
    (hq : ∀ i, ports q'.drawing (k.incidence.vertex i) = (ports q.drawing i).map k.incidence.wire)
    (v : Fin (glue p q).vertices) :
    ports (glue p' q').drawing (gluedVertices h k v) =
      (ports (glue p q).drawing v).map (gluedWires h k) := by
  change ports (matching p' q').glue (gluedVertices h k v) =
    (ports (matching p q).glue v).map (gluedWires h k)
  induction v using Fin.addCases with
  | left i =>
    rw [vertex_left, lo, lo, hp]
    exact (List.map_map ..).trans
      ((congrArg (fun f => (ports p.drawing i).map f) (funext fun x => (glued_left h k x).symm)).trans
        (List.map_map ..).symm)
  | right i =>
    rw [vertex_right, hi, hi, hq]
    exact (List.map_map ..).trans
      ((congrArg (fun f => (ports q.drawing i).map f) (funext fun x => (glued_right h k x).symm)).trans
        (List.map_map ..).symm)

noncomputable def gluedIncidence : (glue p q).drawing.IncidenceEquiv (glue p' q').drawing where
  vertex := gluedVertices h k
  wire := gluedWires h k
  generator := glue_generators h k
  label := glue_labels h k
  inputs := glue_ports h k (fun d => d.inputs) inputs_lower inputs_upper h.incidence.inputs k.incidence.inputs
  outputs := glue_ports h k (fun d => d.outputs) outputs_lower outputs_upper h.incidence.outputs k.incidence.outputs

end Silmaril.RuntimeWires.Proofs.CapClasses
