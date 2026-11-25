module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.CoreTransport
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Knots

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.MiddleAssociator

open ProgressiveGraph CollarAssociator
open EmptyWhiskering (framed frameIncidence framed_pieces compare_piece compare_capPiece
  frame_vertexX frame_vertexHeight lowerUnit)
open CapClasses (incidence_symm incidence_trans)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b a' b' : FixedCap S}
variable (p : FixedDrawing S a.profile b.profile) (q : FixedDrawing S a'.profile b'.profile)
variable (ha : a.types = a'.types) (hb : b.types = b'.types)
variable (D : CoreTransport horizontal p q)

abbrev shift (h : a.types = a'.types) := FixedCap.interpolationDrawing h
abbrev source := framed (lowerUnit a) p (shift hb)
abbrev target := framed (shift ha) q (lowerUnit b')

abbrev sourceIncidence := frameIncidence (lowerUnit a) p (shift hb) rfl rfl
abbrev targetIncidence := frameIncidence (shift ha) q (lowerUnit b') rfl rfl

theorem prefix_point (i : Fin a.profile.size) (t : ℝ) :
    (shift ha).drawing.x ((shift ha).output (D.inputIndex i)).val t =
      interpolate (a.profile.x i) (horizontal (a.profile.x i)) t := by
  have slot := D.input_slot horizontal_strict ha i
  have wire : ((shift ha).output (D.inputIndex i)).val = i :=
    (congrArg (FixedCap.recoordinationSlots ha).symm slot).trans
      ((FixedCap.recoordinationSlots ha).symm_apply_apply i)
  rw [wire]
  exact (FixedCap.interpolation_x ha i t).trans
    (congrArg (fun x => interpolate (a.profile.x i) x t)
      ((congrArg a'.profile.x slot.symm).trans (D.input_x i)))

include D in
theorem suffix_point (i : Fin b.profile.size) (t : ℝ) :
    (shift hb).drawing.x ((shift hb).input i).val t =
      interpolate (b.profile.x i) (horizontal (b.profile.x i)) t :=
  (FixedCap.interpolation_x hb i t).trans
    (congrArg (fun x => interpolate (b.profile.x i) x t)
      ((congrArg b'.profile.x (D.output_slot horizontal_strict hb i).symm).trans (D.output_x i)))

local notation "F" => CapHomeomorph.plane ambient
local notation "E" => D.incidence.wire
local notation "H" => Height.leftPlacement

theorem trace_at (w : Fin p.wires) (z : ℝ × ℝ) :
    z ∈ ((source p hb).drawing.wire ((sourceIncidence p hb).wire w)).trace ↔
      F z ∈ ((target q ha).drawing.wire ((targetIncidence q ha).wire (E w))).trace := by
  refine (framed_pieces (lowerUnit a) p (shift hb) rfl rfl w z).trans <|
    Iff.trans ?_ (framed_pieces (shift ha) q (lowerUnit b') rfl rfl (E w) (F z)).symm
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ ?_)))
  · refine compare_capPiece D.inputIndex E (H 0) F
      (fun i => (p.input i).val) (fun i => (q.input i).val)
      _ _ D.input_wire ?_ w z
    intro i t ht
    have before : (lowerUnit a).drawing.x ((lowerUnit a).output i).val t = a.profile.x i :=
      FixedDrawing.identity_x (S := S) a.inside i t
    change F ((lowerUnit a).drawing.x ((lowerUnit a).output i).val t, H 0 t) =
      ((shift ha).drawing.x ((shift ha).output (D.inputIndex i)).val t, H 0 t)
    rw [before, prefix_point p q ha D]
    simpa [interpolate_zero] using ambient_track (a.inside i) 0 ht
  · refine compare_capPiece D.inputIndex E (H 1) F
      (fun i => (p.input i).val) (fun i => (q.input i).val)
      _ _ D.input_wire ?_ w z
    intro i t ht
    rw [D.input_x]
    simpa [interpolate_zero, interpolate_one] using ambient_track (a.inside i) 1 ht
  · apply compare_piece E E (H 2) F id id _ _ _ _
      (fun _ => rfl) D.covers _ w z
    intro i t ht
    rw [D.wire_x i t ht]
    have inside : p.drawing.x i t ∈ Set.Ioo (0 : ℝ) 1 := p.drawing.wire_inside i t ht
    simpa [interpolate_zero, interpolate_one] using ambient_track
      inside 2 (covers_unit p.drawing ht)
  · refine compare_capPiece D.outputIndex E (H 3) F
      (fun i => (p.output i).val) (fun i => (q.output i).val)
      _ _ D.output_wire ?_ w z
    intro i t ht
    rw [D.output_x]
    simpa [interpolate_zero, interpolate_one] using ambient_track (b.inside i) 3 ht
  · refine compare_capPiece D.outputIndex E (H 4) F
      (fun i => (p.output i).val) (fun i => (q.output i).val)
      _ _ D.output_wire ?_ w z
    intro i t ht
    have after : (lowerUnit b').drawing.x ((lowerUnit b').input (D.outputIndex i)).val t =
        horizontal (b.profile.x i) :=
      (FixedDrawing.identity_x (S := S) b'.inside (D.outputIndex i) t).trans (D.output_x i)
    change F ((shift hb).drawing.x ((shift hb).input i).val t, H 4 t) =
      ((lowerUnit b').drawing.x ((lowerUnit b').input (D.outputIndex i)).val t, H 4 t)
    rw [suffix_point p q hb D i t, after]
    simpa [interpolate_one] using ambient_track (b.inside i) 4 ht

theorem vertex_at (j : Fin p.vertices) :
    F ((source p hb).drawing.vertexX ((sourceIncidence p hb).vertex j),
        (source p hb).drawing.vertexHeight ((sourceIncidence p hb).vertex j)) =
      ((target q ha).drawing.vertexX ((targetIncidence q ha).vertex (D.incidence.vertex j)),
        (target q ha).drawing.vertexHeight ((targetIncidence q ha).vertex (D.incidence.vertex j))) := by
  have src :
      ((source p hb).drawing.vertexX ((sourceIncidence p hb).vertex j),
        (source p hb).drawing.vertexHeight ((sourceIncidence p hb).vertex j)) =
      (p.drawing.vertexX j, H 2 (p.drawing.vertexHeight j)) :=
    Prod.ext (frame_vertexX (lowerUnit a) p (shift hb) rfl rfl j)
      (frame_vertexHeight (lowerUnit a) p (shift hb) rfl rfl j)
  let k := D.incidence.vertex j
  have dst :
      ((target q ha).drawing.vertexX ((targetIncidence q ha).vertex k),
        (target q ha).drawing.vertexHeight ((targetIncidence q ha).vertex k)) =
      (horizontal (p.drawing.vertexX j), H 2 (p.drawing.vertexHeight j)) :=
    Prod.ext
      ((frame_vertexX (shift ha) q (lowerUnit b') rfl rfl k).trans (D.vertex_x j))
      ((frame_vertexHeight (shift ha) q (lowerUnit b') rfl rfl k).trans (congrArg (H 2) (D.vertex_height j)))
  have mid : F (p.drawing.vertexX j, H 2 (p.drawing.vertexHeight j)) =
      (horizontal (p.drawing.vertexX j), H 2 (p.drawing.vertexHeight j)) := by
    simpa [interpolate_zero, interpolate_one] using ambient_track
      (p.drawing.vertex_inside j).1 2 (Set.Ioo_subset_Icc_self (p.drawing.vertex_inside j).2)
  exact (congrArg F src).trans (mid.trans dst.symm)

/-- Compare the actual five pieces after padding has aligned the middle
slab. The input and output matches come from ordered geometric incidence. -/
def framedComparison : (source p hb).drawing.CapComparison (target q ha).drawing where
  map := ambient
  incidence := incidence_trans (incidence_symm (sourceIncidence p hb))
    (incidence_trans D.incidence (targetIncidence q ha))
  trace w := by
    obtain ⟨i, rfl⟩ := (sourceIncidence p hb).wire.surjective w
    change F '' ((source p hb).drawing.wire ((sourceIncidence p hb).wire i)).trace =
      ((target q ha).drawing.wire
        ((targetIncidence q ha).wire (E ((sourceIncidence p hb).wire.symm ((sourceIncidence p hb).wire i))))).trace
    rw [Equiv.symm_apply_apply]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (trace_at p q ha hb D i x).mp hx
    · intro hz
      refine ⟨(F).symm z, (trace_at p q ha hb D i _).mpr ?_, (F).apply_symm_apply z⟩
      rwa [Homeomorph.apply_symm_apply]
  vertex v := by
    obtain ⟨j, rfl⟩ := (sourceIncidence p hb).vertex.surjective v
    change F ((source p hb).drawing.vertexX ((sourceIncidence p hb).vertex j),
        (source p hb).drawing.vertexHeight ((sourceIncidence p hb).vertex j)) =
      ((target q ha).drawing.vertexX ((targetIncidence q ha).vertex
          (D.incidence.vertex ((sourceIncidence p hb).vertex.symm ((sourceIncidence p hb).vertex j)))),
        (target q ha).drawing.vertexHeight ((targetIncidence q ha).vertex
          (D.incidence.vertex ((sourceIncidence p hb).vertex.symm ((sourceIncidence p hb).vertex j)))))
    rw [Equiv.symm_apply_apply]
    exact vertex_at p q ha hb D j

end Silmaril.RuntimeWires.Proofs.MiddleAssociator
