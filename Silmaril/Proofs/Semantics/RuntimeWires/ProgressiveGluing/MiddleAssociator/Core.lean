module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.CoreTransport
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Knots
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Drawing

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.MiddleAssociator

open ProgressiveGraph
open HorizontalPlacement (adjoin placed drawing placedWires wire_x_active wire_x_idle
  wire_data_active wire_data_idle LocatedWire start_active finish_active)
open HorizontalComparison (drawing_inputs drawing_outputs)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {B D : FixedCap S}

section Placement

variable {V W : ℕ} (s : ActiveStrip) (d : ProgressiveGraph.Diagram S V W .point) (J : FixedCap S)

theorem active_covers (w : Fin W) (y : ℝ) :
    (drawing s d J).covers (Fin.castAdd J.profile.size w) y ↔ d.covers w y := by
  simp only [ProgressiveGraph.Diagram.covers, ProgressiveGraph.Diagram.lower,
    ProgressiveGraph.Diagram.upper, start_active, finish_active]
  rfl

theorem active_data (w : Fin W) (y : ℝ) :
    ((drawing s d J).label (Fin.castAdd J.profile.size w),
        (drawing s d J).x (Fin.castAdd J.profile.size w) y) =
      (d.label w, s.place (d.x w y)) :=
  Prod.ext (congrArg LocatedWire.label (wire_data_active s d J w)) (wire_x_active s d J w y)

theorem idle_data (i : Fin J.profile.size) (y : ℝ) :
    ((drawing s d J).label (Fin.natAdd W i), (drawing s d J).x (Fin.natAdd W i) y) =
      (J.profile.label i, s.opposite.place (J.profile.x i)) :=
  Prod.ext (congrArg LocatedWire.label (wire_data_idle s d J i)) (wire_x_idle s d J i y)

end Placement

variable (A C : FixedCap S) (p : FixedDrawing S B.profile D.profile)

abbrev leftInner := placed .right A (a := B) (b := D) p
abbrev rightInner := placed .left C (a := B) (b := D) p
abbrev leftCore := placed .left C (a := adjoin .right B A) (b := adjoin .right D A) (leftInner A p)
abbrev rightCore := placed .right A (a := adjoin .left B C) (b := adjoin .left D C) (rightInner C p)

abbrev WireNames := Fin p.wires ⊕ (Fin A.profile.size ⊕ Fin C.profile.size)

/-- Allocation is active first, then the inner idle block, then the outer idle block.
The common enumeration names a wire by its original drawing or idle profile. -/
def leftNames : WireNames A C p ≃ Fin (leftCore A C p).wires :=
  (Equiv.sumAssoc _ _ _).symm.trans
    ((finSumFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv)

def rightNames : WireNames A C p ≃ Fin (rightCore A C p).wires :=
  ((Equiv.refl _).sumCongr (Equiv.sumComm _ _)).trans
    ((Equiv.sumAssoc _ _ _).symm.trans
      ((finSumFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv))

def renameWires : Fin (leftCore A C p).wires ≃ Fin (rightCore A C p).wires :=
  (leftNames A C p).symm.trans (rightNames A C p)

theorem rename_at (w : WireNames A C p) :
    renameWires A C p (leftNames A C p w) = rightNames A C p w := by
  simp only [renameWires, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem left_active (w : Fin p.wires) :
    leftNames A C p (.inl w) = Fin.castAdd C.profile.size (Fin.castAdd A.profile.size w) := rfl

theorem right_active (w : Fin p.wires) :
    rightNames A C p (.inl w) = Fin.castAdd A.profile.size (Fin.castAdd C.profile.size w) := rfl

theorem left_wireData (w : WireNames A C p) (y : ℝ) :
    ((leftCore A C p).drawing.label (leftNames A C p w), (leftCore A C p).drawing.x (leftNames A C p w) y) =
      match w with
      | .inl i => (p.drawing.label i, ActiveStrip.left.place (ActiveStrip.right.place (p.drawing.x i y)))
      | .inr (.inl i) => (A.profile.label i, ActiveStrip.left.place (ActiveStrip.left.place (A.profile.x i)))
      | .inr (.inr i) => (C.profile.label i, ActiveStrip.right.place (C.profile.x i)) := by
  rcases w with i | (i | i)
  · exact (active_data .left (leftInner A p).drawing C _ y).trans
      (congrArg (fun z => (z.1, ActiveStrip.left.place z.2)) (active_data .right p.drawing A i y))
  · exact (active_data .left (leftInner A p).drawing C _ y).trans
      (congrArg (fun z => (z.1, ActiveStrip.left.place z.2)) (idle_data .right p.drawing A i y))
  · exact idle_data .left (leftInner A p).drawing C i y

theorem right_wireData (w : WireNames A C p) (y : ℝ) :
    ((rightCore A C p).drawing.label (rightNames A C p w), (rightCore A C p).drawing.x (rightNames A C p w) y) =
      match w with
      | .inl i => (p.drawing.label i, ActiveStrip.right.place (ActiveStrip.left.place (p.drawing.x i y)))
      | .inr (.inl i) => (A.profile.label i, ActiveStrip.left.place (A.profile.x i))
      | .inr (.inr i) => (C.profile.label i, ActiveStrip.right.place (ActiveStrip.right.place (C.profile.x i))) := by
  rcases w with i | (i | i)
  · exact (active_data .right (rightInner C p).drawing A _ y).trans
      (congrArg (fun z => (z.1, ActiveStrip.right.place z.2)) (active_data .left p.drawing C i y))
  · exact idle_data .right (rightInner C p).drawing A i y
  · exact (active_data .right (rightInner C p).drawing A _ y).trans
      (congrArg (fun z => (z.1, ActiveStrip.right.place z.2)) (idle_data .left p.drawing C i y))

theorem core_label (w : Fin (leftCore A C p).wires) :
    (rightCore A C p).drawing.label (renameWires A C p w) = (leftCore A C p).drawing.label w := by
  obtain ⟨w, rfl⟩ := (leftNames A C p).surjective w
  rw [rename_at]
  rcases w with i | (i | i)
  · exact (congrArg Prod.fst (right_wireData A C p (.inl i) 0)).trans
      (congrArg Prod.fst (left_wireData A C p (.inl i) 0)).symm
  · exact (congrArg Prod.fst (right_wireData A C p (.inr (.inl i)) 0)).trans
      (congrArg Prod.fst (left_wireData A C p (.inr (.inl i)) 0)).symm
  · exact (congrArg Prod.fst (right_wireData A C p (.inr (.inr i)) 0)).trans
      (congrArg Prod.fst (left_wireData A C p (.inr (.inr i)) 0)).symm

theorem core_x (w : Fin (leftCore A C p).wires) (y : ℝ) (h : (leftCore A C p).drawing.covers w y) :
    (rightCore A C p).drawing.x (renameWires A C p w) y = horizontal ((leftCore A C p).drawing.x w y) := by
  obtain ⟨w, rfl⟩ := (leftNames A C p).surjective w
  rw [rename_at]
  have left := congrArg Prod.snd (left_wireData A C p w y)
  have right := congrArg Prod.snd (right_wireData A C p w y)
  refine right.trans (Eq.trans ?_ (congrArg horizontal left).symm)
  cases w with
  | inl i =>
    have hi := (active_covers .left (leftInner A p).drawing C _ y).mp h
    have hp := (active_covers .right p.drawing A i y).mp hi
    exact (horizontal_middle (Set.Ioo_subset_Icc_self (p.drawing.wire_inside i y hp))).symm
  | inr w =>
    cases w with
    | inl i => exact (horizontal_left (Set.Ioo_subset_Icc_self (A.inside i))).symm
    | inr i => exact (horizontal_right (Set.Ioo_subset_Icc_self (C.inside i))).symm

theorem rename_ports (xs : List (Fin p.wires)) :
    xs.map (fun w => rightNames A C p (.inl w)) =
      (xs.map (fun w => leftNames A C p (.inl w))).map (renameWires A C p) :=
  (congrArg (fun f => xs.map f) (funext fun w => (rename_at A C p (.inl w)).symm)).trans
    (List.map_map ..).symm

theorem left_inputs (j : Fin p.vertices) :
    (leftCore A C p).drawing.inputs j =
      (p.drawing.inputs j).map (fun w => leftNames A C p (.inl w)) :=
  (drawing_inputs .left C (leftInner A p).drawing j).trans
    ((congrArg (List.map (Fin.castAdd C.profile.size)) (drawing_inputs .right A p.drawing j)).trans
      ((List.map_map ..).trans
        (congrArg (fun f => (p.drawing.inputs j).map f) (funext fun w => (left_active A C p w).symm))))

theorem right_inputs (j : Fin p.vertices) :
    (rightCore A C p).drawing.inputs j =
      (p.drawing.inputs j).map (fun w => rightNames A C p (.inl w)) :=
  (drawing_inputs .right A (rightInner C p).drawing j).trans
    ((congrArg (List.map (Fin.castAdd A.profile.size)) (drawing_inputs .left C p.drawing j)).trans
      ((List.map_map ..).trans
        (congrArg (fun f => (p.drawing.inputs j).map f) (funext fun w => (right_active A C p w).symm))))

theorem left_outputs (j : Fin p.vertices) :
    (leftCore A C p).drawing.outputs j =
      (p.drawing.outputs j).map (fun w => leftNames A C p (.inl w)) :=
  (drawing_outputs .left C (leftInner A p).drawing j).trans
    ((congrArg (List.map (Fin.castAdd C.profile.size)) (drawing_outputs .right A p.drawing j)).trans
      ((List.map_map ..).trans
        (congrArg (fun f => (p.drawing.outputs j).map f) (funext fun w => (left_active A C p w).symm))))

theorem right_outputs (j : Fin p.vertices) :
    (rightCore A C p).drawing.outputs j =
      (p.drawing.outputs j).map (fun w => rightNames A C p (.inl w)) :=
  (drawing_outputs .right A (rightInner C p).drawing j).trans
    ((congrArg (List.map (Fin.castAdd A.profile.size)) (drawing_outputs .left C p.drawing j)).trans
      ((List.map_map ..).trans
        (congrArg (fun f => (p.drawing.outputs j).map f) (funext fun w => (right_active A C p w).symm))))

def coreIncidence : (leftCore A C p).drawing.IncidenceEquiv (rightCore A C p).drawing where
  vertex := Equiv.refl _
  wire := renameWires A C p
  generator _ := rfl
  label := core_label A C p
  inputs j := (right_inputs A C p j).trans ((rename_ports A C p _).trans
    (congrArg (List.map (renameWires A C p)) (left_inputs A C p j)).symm)
  outputs j := (right_outputs A C p j).trans ((rename_ports A C p _).trans
    (congrArg (List.map (renameWires A C p)) (left_outputs A C p j)).symm)

def coreTransport :
    CoreTransport horizontal (leftCore A C p) (rightCore A C p) where
  incidence := coreIncidence A C p
  vertex_x j :=
    (horizontal_middle (Set.Ioo_subset_Icc_self (p.drawing.vertex_inside j).1)).symm
  vertex_height _ := rfl
  wire_x := core_x A C p

end Silmaril.RuntimeWires.Proofs.MiddleAssociator
