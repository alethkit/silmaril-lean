module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Matching
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Wires
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CapRecoordination.Regression

open ProgressiveGraph CategoryTheory
open CollarAssociator (leftWire inputCap inputCap_val wire_contact)

private abbrev signature : Signature Bool where
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

private def cap (x : Fin 3 → ℝ) (ordered : StrictMono x)
    (inside : ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1) : FixedCap signature :=
  ⟨⟨3, ![false, true, false], x, ordered⟩, inside⟩

private def original : FixedCap signature :=
  cap ![1 / 8, 1 / 3, 3 / 4]
    (Fin.strictMono_iff_lt_succ.mpr (by intro i; fin_cases i <;> norm_num [Fin.castSucc, Fin.succ]))
    (by intro i; fin_cases i <;> norm_num)

private def shifted : FixedCap signature :=
  cap ![1 / 4, 1 / 2, 7 / 8]
    (Fin.strictMono_iff_lt_succ.mpr (by intro i; fin_cases i <;> norm_num [Fin.castSucc, Fin.succ]))
    (by intro i; fin_cases i <;> norm_num)

private theorem same_types : original.types = shifted.types := rfl

private abbrev forward := FixedCap.interpolationDrawing same_types
private abbrev backward := FixedCap.interpolationDrawing same_types.symm

/-- At midheight the three ordered typed strands move by unequal amounts. -/
example :
    (forward.drawing.x (0 : Fin 3) (1 / 2), forward.drawing.x (1 : Fin 3) (1 / 2),
      forward.drawing.x (2 : Fin 3) (1 / 2)) = (3 / 16, 5 / 12, 13 / 16) := by
  refine Prod.ext ((FixedCap.interpolation_x same_types (0 : Fin 3) _).trans ?_)
    (Prod.ext ((FixedCap.interpolation_x same_types (1 : Fin 3) _).trans ?_)
      ((FixedCap.interpolation_x same_types (2 : Fin 3) _).trans ?_))
  · change interpolate (1 / 8) (1 / 4) (1 / 2) = 3 / 16
    norm_num [interpolate]
  · change interpolate (1 / 3) (1 / 2) (1 / 2) = 5 / 12
    norm_num [interpolate]
  · change interpolate (3 / 4) (7 / 8) (1 / 2) = 13 / 16
    norm_num [interpolate]

private abbrev roundTrip := forward.thenDo backward
private abbrev identity := FixedDrawing.identity signature original.profile original.inside
private abbrev roundComparison := roundTrip.compareVertexFree identity (by rfl) rfl

private theorem splice_first : roundTrip.drawing.x (roundTrip.input (0 : Fin 3)).val (1 / 4) = 1 / 4 := by
  let m := CapClasses.matching forward backward
  have name : (roundTrip.input (0 : Fin 3)).val = leftWire m (forward.output (0 : Fin 3)).val := by
    change (inputCap m (forward.input (0 : Fin 3))).val = _
    rw [inputCap_val]
    rfl
  change m.glue.x ((roundTrip.input (0 : Fin 3)).val) (1 / 4) = _
  rw [name, wire_contact m]
  refine (m.glue_x_in_collar (forward.output (0 : Fin 3)) (by constructor <;> norm_num)).trans ?_
  have lower : forward.drawing.x (forward.output (0 : Fin 3)).val 1 = 1 / 4 :=
    forward.output_x (0 : Fin 3)
  have upper : backward.drawing.x (m.contact (forward.output (0 : Fin 3))).val 0 = 1 / 4 :=
    (congrArg (fun w => backward.drawing.x w.val 0)
      (CapClasses.match_slot forward backward (0 : Fin 3))).trans (backward.input_x (0 : Fin 3))
  exact (congrArg₂ (fun x z => interpolate x z (4 * (1 / 4) - 1)) lower upper).trans
    (by norm_num [interpolate])

private theorem roundTrip_point :
    roundComparison.map.plane (1 / 4, 1 / 4) = (1 / 8, 1 / 4) := by
  have h := roundTrip.compareVertexFree_point identity (by rfl) rfl (0 : Fin 3)
    (y := 1 / 4) (by constructor <;> norm_num)
  have straight : identity.drawing.x (identity.input (0 : Fin 3)).val (1 / 4) = 1 / 8 :=
    FixedDrawing.identity_x (S := signature) original.inside (0 : Fin 3) (1 / 4)
  calc
    _ = roundComparison.map.plane (roundTrip.drawing.x (roundTrip.input (0 : Fin 3)).val (1 / 4), 1 / 4) :=
      congrArg (fun x => roundComparison.map.plane (x, 1 / 4)) splice_first.symm
    _ = (identity.drawing.x (identity.input (0 : Fin 3)).val (1 / 4), 1 / 4) := h
    _ = _ := congrArg (fun x : ℝ => (x, (1 / 4 : ℝ))) straight

example : roundComparison.map.plane.symm (1 / 8, 1 / 4) = (1 / 4, 1 / 4) := by
  rw [← roundTrip_point, Homeomorph.symm_apply_apply]

example :
    (FixedCap.recoordinateIso same_types).hom ≫ (FixedCap.recoordinateIso same_types).inv =
      𝟙 original :=
  (FixedCap.recoordinateIso same_types).hom_inv_id

example :
    (FixedCap.recoordinateIso same_types).inv ≫ (FixedCap.recoordinateIso same_types).hom =
      𝟙 shifted :=
  (FixedCap.recoordinateIso same_types).inv_hom_id

/-- The empty right neighbor still rescales each coordinate into the left half. -/
private def halfStrip := original.beside (FixedCap.empty signature)

private theorem half_types : original.types = halfStrip.types := by
  change List.ofFn original.profile.label = List.ofFn (original.beside (FixedCap.empty signature)).profile.label
  rw [FixedCap.beside_labels]
  rfl

example : halfStrip.profile.x (0 : Fin 3) < original.profile.x (0 : Fin 3) := by
  change ActiveStrip.left.place (1 / 8) < (1 / 8 : ℝ)
  norm_num [ActiveStrip.place]

example : original ≅ halfStrip :=
  FixedCap.recoordinateIso half_types

example :
    FixedCap.recoordinate same_types ≫ FixedCap.recoordinate (same_types.symm.trans half_types) =
      FixedCap.recoordinate half_types :=
  FixedCap.recoordinate_comp same_types (same_types.symm.trans half_types)

end Silmaril.RuntimeWires.Proofs.CapRecoordination.Regression
