module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Placement
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Trace
import Mathlib.Tactic.NormNum

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.EmptyWhiskering

open ProgressiveGraph CollarAssociator
open HorizontalComparison (InteriorRange drawnXs common_range wire_in_drawnXs vertex_in_drawnXs)
open CapClasses (incidence_symm incidence_trans)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} (side : ActiveStrip) {a b : FixedCap S}
variable (p : FixedDrawing S a.profile b.profile)

abbrev lowerUnit (a : FixedCap S) := FixedDrawing.identity S a.profile a.inside
abbrev source := framed (lowerUnit a) p (shift side b)
abbrev target := framed (shift side a) (placedCore side p) (lowerUnit (placedCap side b))

abbrev sourceIncidence := frameIncidence (lowerUnit a) p (shift side b) rfl rfl
abbrev targetIncidence := frameIncidence (shift side a) (placedCore side p) (lowerUnit (placedCap side b)) rfl rfl

theorem input_cover (i : Fin a.profile.size) : p.drawing.covers (p.input i).val 0 := by
  have lo : p.drawing.lower (p.input i).val = 0 := by
    simp only [Diagram.lower, endpointHeight, (p.input i).property, Option.elim_none]
  exact ⟨lo.le, lo ▸ (p.drawing.wire (p.input i).val).increasing.le⟩

theorem output_cover (i : Fin b.profile.size) : p.drawing.covers (p.output i).val 1 := by
  have hi : p.drawing.upper (p.output i).val = 1 := by
    simp only [Diagram.upper, endpointHeight, (p.output i).property, Option.elim_none]
  exact ⟨hi ▸ (p.drawing.wire (p.output i).val).increasing.le, hi.ge⟩

variable (span : InteriorRange) (bound : drawnXs p.drawing ⊆ Set.Icc span.left span.right)

include bound in
theorem input_range (i : Fin a.profile.size) : a.profile.x i ∈ Set.Icc span.left span.right :=
  p.input_x i ▸ bound (wire_in_drawnXs p.drawing (p.input i).val (input_cover p i))

include bound in
theorem output_range (i : Fin b.profile.size) : b.profile.x i ∈ Set.Icc span.left span.right :=
  p.output_x i ▸ bound (wire_in_drawnXs p.drawing (p.output i).val (output_cover p i))

local notation "F" => CapHomeomorph.plane (ambient side span)
local notation "E" => placedWires side p
local notation "H" => Height.leftPlacement

include bound in
theorem trace_at (w : Fin p.wires) (z : ℝ × ℝ) :
    z ∈ ((source side p).drawing.wire ((sourceIncidence side p).wire w)).trace ↔
      F z ∈ ((target side p).drawing.wire ((targetIncidence side p).wire (E w))).trace := by
  refine (framed_pieces (lowerUnit a) p (shift side b) rfl rfl w z).trans <|
    Iff.trans ?_ (framed_pieces (shift side a) (placedCore side p) (lowerUnit (placedCap side b))
      rfl rfl (E w) (F z)).symm
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ ?_)))
  · refine compare_capPiece (slot side a) E (H 0) F
      (fun i => (p.input i).val) (fun i => ((placedCore side p).input i).val)
      _ _ (placed_input side p) ?_ w z
    intro i t ht
    have src := FixedDrawing.identity_x (S := S) a.inside i t
    have dst : (shift side a).drawing.x ((shift side a).output (slot side a i)).val t =
        track side t (a.profile.x i) :=
      (congrArg (fun j => (shift side a).drawing.x j t) (shift_output side a i)).trans (shift_x side a i t)
    change F ((lowerUnit a).drawing.x ((lowerUnit a).output i).val t, H 0 t) =
      ((shift side a).drawing.x ((shift side a).output (slot side a i)).val t, H 0 t)
    rw [show (lowerUnit a).drawing.x ((lowerUnit a).output i).val t = a.profile.x i from src, dst]
    simpa [track_zero] using ambient_track side span (input_range p span bound i) 0 ht
  · refine compare_capPiece (slot side a) E (H 1) F
      (fun i => (p.input i).val) (fun i => ((placedCore side p).input i).val)
      _ _ (placed_input side p) ?_ w z
    intro i t ht
    rw [slot_x]
    simpa [track_zero, track_one] using ambient_track side span (input_range p span bound i) 1 ht
  · apply compare_piece E E (H 2) F id id _ _ _ _
      (fun _ => rfl) (placed_covers side p) _ w z
    intro i t ht
    change F (p.drawing.x i t, H 2 t) = ((placedCore side p).drawing.x (E i) t, H 2 t)
    rw [placed_x]
    simpa [track_zero, track_one] using ambient_track side span
      (bound (wire_in_drawnXs p.drawing i ht)) 2 (covers_unit p.drawing ht)
  · refine compare_capPiece (slot side b) E (H 3) F
      (fun i => (p.output i).val) (fun i => ((placedCore side p).output i).val)
      _ _ (placed_output side p) ?_ w z
    intro i t ht
    change F (b.profile.x i, H 3 t) = ((placedCap side b).profile.x (slot side b i), H 3 t)
    rw [slot_x]
    simpa [track_zero, track_one] using ambient_track side span (output_range p span bound i) 3 ht
  · refine compare_capPiece (slot side b) E (H 4) F
      (fun i => (p.output i).val) (fun i => ((placedCore side p).output i).val)
      _ _ (placed_output side p) ?_ w z
    intro i t ht
    have src : (shift side b).drawing.x ((shift side b).input i).val t = track side t (b.profile.x i) :=
      (congrArg (fun j => (shift side b).drawing.x j t) (shift_input side b i)).trans (shift_x side b i t)
    have dst : (lowerUnit (placedCap side b)).drawing.x
        ((lowerUnit (placedCap side b)).input (slot side b i)).val t = side.place (b.profile.x i) :=
      (FixedDrawing.identity_x (S := S) (placedCap side b).inside (slot side b i) t).trans (slot_x side b i)
    change F ((shift side b).drawing.x ((shift side b).input i).val t, H 4 t) =
      ((lowerUnit (placedCap side b)).drawing.x ((lowerUnit (placedCap side b)).input (slot side b i)).val t, H 4 t)
    rw [src, dst]
    simpa [track_one] using ambient_track side span (output_range p span bound i) 4 ht

include bound in
theorem vertex_at (j : Fin p.vertices) :
    F ((source side p).drawing.vertexX ((sourceIncidence side p).vertex j),
        (source side p).drawing.vertexHeight ((sourceIncidence side p).vertex j)) =
      ((target side p).drawing.vertexX ((targetIncidence side p).vertex ((placedIncidence side p).vertex j)),
        (target side p).drawing.vertexHeight ((targetIncidence side p).vertex ((placedIncidence side p).vertex j))) := by
  have src :
      ((source side p).drawing.vertexX ((sourceIncidence side p).vertex j),
        (source side p).drawing.vertexHeight ((sourceIncidence side p).vertex j)) =
      (p.drawing.vertexX j, H 2 (p.drawing.vertexHeight j)) :=
    Prod.ext (frame_vertexX (lowerUnit a) p (shift side b) rfl rfl j)
      (frame_vertexHeight (lowerUnit a) p (shift side b) rfl rfl j)
  let k := (placedIncidence side p).vertex j
  have dst :
      ((target side p).drawing.vertexX ((targetIncidence side p).vertex k),
        (target side p).drawing.vertexHeight ((targetIncidence side p).vertex k)) =
      (side.place (p.drawing.vertexX j), H 2 (p.drawing.vertexHeight j)) :=
    Prod.ext
      ((frame_vertexX (shift side a) (placedCore side p) (lowerUnit (placedCap side b)) rfl rfl k).trans
        (placed_vertexX side p j))
      ((frame_vertexHeight (shift side a) (placedCore side p) (lowerUnit (placedCap side b)) rfl rfl k).trans
        (congrArg (H 2) (placed_vertexHeight side p j)))
  have mid : F (p.drawing.vertexX j, H 2 (p.drawing.vertexHeight j)) =
      (side.place (p.drawing.vertexX j), H 2 (p.drawing.vertexHeight j)) := by
    simpa [track_zero, track_one] using ambient_track side span
      (bound (vertex_in_drawnXs p.drawing j)) 2 (Set.Ioo_subset_Icc_self (p.drawing.vertex_inside j).2)
  exact (congrArg F src).trans (mid.trans dst.symm)

def framedComparison : (source side p).drawing.CapComparison (target side p).drawing where
  map := ambient side span
  incidence := incidence_trans (incidence_symm (sourceIncidence side p))
    (incidence_trans (placedIncidence side p) (targetIncidence side p))
  trace w := by
    obtain ⟨i, rfl⟩ := (sourceIncidence side p).wire.surjective w
    change F '' ((source side p).drawing.wire ((sourceIncidence side p).wire i)).trace =
      ((target side p).drawing.wire
        ((targetIncidence side p).wire (E ((sourceIncidence side p).wire.symm ((sourceIncidence side p).wire i))))).trace
    rw [Equiv.symm_apply_apply]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (trace_at side p span bound i x).mp hx
    · intro hz
      refine ⟨(F).symm z, (trace_at side p span bound i _).mpr ?_, (F).apply_symm_apply z⟩
      rwa [Homeomorph.apply_symm_apply]
  vertex v := by
    obtain ⟨j, rfl⟩ := (sourceIncidence side p).vertex.surjective v
    change F ((source side p).drawing.vertexX ((sourceIncidence side p).vertex j),
        (source side p).drawing.vertexHeight ((sourceIncidence side p).vertex j)) =
      ((target side p).drawing.vertexX ((targetIncidence side p).vertex
          ((placedIncidence side p).vertex ((sourceIncidence side p).vertex.symm ((sourceIncidence side p).vertex j)))),
        (target side p).drawing.vertexHeight ((targetIncidence side p).vertex
          ((placedIncidence side p).vertex ((sourceIncidence side p).vertex.symm ((sourceIncidence side p).vertex j)))))
    rw [Equiv.symm_apply_apply]
    exact vertex_at side p span bound j

def compare : (source side p).drawing.CapComparison (target side p).drawing :=
  framedComparison side p (Classical.choose (common_range p.drawing p.drawing))
    (Classical.choose_spec (common_range p.drawing p.drawing)).1

end Silmaril.RuntimeWires.Proofs.EmptyWhiskering
