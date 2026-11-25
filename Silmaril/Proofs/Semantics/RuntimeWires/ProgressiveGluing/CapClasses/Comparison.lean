module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Homeomorph
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Associator.Thms

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.CapClasses

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W V' W' V'' W'' : ℕ}
variable {a : ProgressiveGraph.Diagram S V W .point} {b : ProgressiveGraph.Diagram S V' W' .point}
variable {c : ProgressiveGraph.Diagram S V'' W'' .point}

def incidence_id (a : ProgressiveGraph.Diagram S V W .point) : a.IncidenceEquiv a where
  vertex := Equiv.refl _
  wire := Equiv.refl _
  generator _ := rfl
  label _ := rfl
  inputs _ := by simp
  outputs _ := by simp

theorem mapped_inverse {I J : Type*} (e : I ≃ J) {x : List I} {y : List J}
    (h : y = x.map e) : x = y.map e.symm := by
  rw [h, List.map_map]
  simp

def incidence_symm (p : a.IncidenceEquiv b) : b.IncidenceEquiv a where
  vertex := p.vertex.symm
  wire := p.wire.symm
  generator i := by simpa using (p.generator (p.vertex.symm i)).symm
  label i := by simpa using (p.label (p.wire.symm i)).symm
  inputs i := by
    have h := p.inputs (p.vertex.symm i)
    rw [Equiv.apply_symm_apply] at h
    exact mapped_inverse p.wire h
  outputs i := by
    have h := p.outputs (p.vertex.symm i)
    rw [Equiv.apply_symm_apply] at h
    exact mapped_inverse p.wire h

def incidence_trans (p : a.IncidenceEquiv b) (q : b.IncidenceEquiv c) : a.IncidenceEquiv c where
  vertex := p.vertex.trans q.vertex
  wire := p.wire.trans q.wire
  generator i := (q.generator (p.vertex i)).trans (p.generator i)
  label i := (q.label (p.wire i)).trans (p.label i)
  inputs i := by
    change c.inputs (q.vertex (p.vertex i)) = _
    rw [q.inputs, p.inputs, List.map_map]
    rfl
  outputs i := by
    change c.outputs (q.vertex (p.vertex i)) = _
    rw [q.outputs, p.outputs, List.map_map]
    rfl

def compare_id (a : ProgressiveGraph.Diagram S V W .point) : a.CapComparison a where
  map := identity
  incidence := incidence_id a
  trace w := by
    change id '' (a.wire w).trace = _
    exact Set.image_id _
  vertex _ := rfl

def compare_symm (p : a.CapComparison b) : b.CapComparison a where
  map := symm p.map
  incidence := incidence_symm p.incidence
  trace w := by
    change p.map.plane.symm '' (b.wire w).trace = (a.wire (p.incidence.wire.symm w)).trace
    have h := p.trace (p.incidence.wire.symm w)
    rw [Equiv.apply_symm_apply] at h
    rw [← h, Set.image_image]
    simp only [Homeomorph.symm_apply_apply, Set.image_id']
  vertex j := by
    change p.map.plane.symm (b.vertexX j, b.vertexHeight j) = _
    have h := p.vertex (p.incidence.vertex.symm j)
    rw [Equiv.apply_symm_apply] at h
    rw [← h, Homeomorph.symm_apply_apply]
    rfl

def compare_trans (p : a.CapComparison b) (q : b.CapComparison c) : a.CapComparison c where
  map := trans p.map q.map
  incidence := incidence_trans p.incidence q.incidence
  trace w := by
    calc
      _ = q.map.plane '' (p.map.plane '' (a.wire w).trace) :=
        (Set.image_image q.map.plane p.map.plane _).symm
      _ = _ := by
        rw [p.trace, q.trace]
        rfl
  vertex j := by
    change q.map.plane (p.map.plane (a.vertexX j, a.vertexHeight j)) = _
    rw [p.vertex, q.vertex]
    rfl

theorem compare_point (p : a.CapComparison b) (w : Fin W) {y : ℝ} (h : a.covers w y) :
    b.covers (p.incidence.wire w) (p.map.height y) ∧
    p.map.plane (a.x w y, y) = (b.x (p.incidence.wire w) (p.map.height y), p.map.height y) := by
  have member : p.map.plane (a.x w y, y) ∈ (b.wire (p.incidence.wire w)).trace := by
    rw [← p.trace w]
    exact ⟨_, ⟨y, h, rfl⟩, rfl⟩
  obtain ⟨z, cover, point⟩ := member
  have hz : z = p.map.height y := (congrArg Prod.snd point).trans (p.map.height_eq _)
  subst z
  exact ⟨cover, point.symm⟩

theorem cap_x (p : a.CapComparison b) (w : Fin W) {y : ℝ} (cover : a.covers w y)
    (outside : y ≤ 0 ∨ 1 ≤ y) : b.x (p.incidence.wire w) y = a.x w y := by
  have fixed := p.map.outside (a.x w y, y) outside
  have hy : p.map.height y = y := (p.map.height_eq _).symm.trans (congrArg Prod.snd fixed)
  have h := (compare_point p w cover).2
  rw [fixed, hy] at h
  exact (congrArg Prod.fst h).symm

theorem input_x (p : a.CapComparison b) (w : Fin W) (h : a.start w = none) :
    b.x (p.incidence.wire w) 0 = a.x w 0 := by
  have start : a.lower w = 0 := by simp [ProgressiveGraph.Diagram.lower, endpointHeight, h]
  exact cap_x p w ⟨start.le, start ▸ (a.wire w).increasing.le⟩ (.inl le_rfl)

theorem output_x (p : a.CapComparison b) (w : Fin W) (h : a.finish w = none) :
    b.x (p.incidence.wire w) 1 = a.x w 1 := by
  have finish : a.upper w = 1 := by simp [ProgressiveGraph.Diagram.upper, endpointHeight, h]
  exact cap_x p w ⟨finish ▸ (a.wire w).increasing.le, finish.ge⟩ (.inr le_rfl)

def motion_comparison (p : a.AmbientMotion) (t : SlabIsotopy.Time) : a.CapComparison (p.drawing t) where
  map :=
    { plane := p.isotopy.frame t
      height := Homeomorph.refl _
      increasing := strictMono_id
      height_eq z := p.isotopy.height t z
      outside z := p.isotopy.outside t z }
  incidence :=
    { vertex := Equiv.refl _
      wire := (p.correspondence t).rename
      generator j := congrFun (p.correspondence t).generators j
      label := (p.correspondence t).label
      inputs := (p.correspondence t).inputs
      outputs := (p.correspondence t).outputs }
  trace := (p.correspondence t).trace
  vertex := (p.correspondence t).vertex

variable {L M R A B C : ℕ}
variable {d : ProgressiveGraph.Diagram S L A .point} {e : ProgressiveGraph.Diagram S M B .point}
variable {f : ProgressiveGraph.Diagram S R C .point}

noncomputable def assoc_comparison (m : d.OrderedVerticalMatch e) (n : e.OrderedVerticalMatch f) :
    (m.attachAfter n).glue.CapComparison (m.attachBefore n).glue where
  map :=
    { plane := ProgressiveGraph.Diagram.OrderedVerticalMatch.assocHeight
      height := CollarAssociator.Height.heightMap
      increasing := by
        intro a b h
        simp only [CollarAssociator.Height.heightMap, OrderedKnots.homeomorph_apply]
        exact OrderedKnots.transfer_strictMono CollarAssociator.Height.left_order CollarAssociator.Height.right_order h
      height_eq _ := by rfl
      outside z h := ProgressiveGraph.Diagram.OrderedVerticalMatch.assocHeight_fixed z h }
  incidence := m.assocIncidence n
  trace := m.assoc_trace n
  vertex := m.assoc_vertex n

end Silmaril.RuntimeWires.Proofs.CapClasses
