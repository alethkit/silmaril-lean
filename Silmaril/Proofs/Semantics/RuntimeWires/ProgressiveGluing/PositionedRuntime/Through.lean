module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import Mathlib.Tactic.Ring

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.PositionedRuntime

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

private theorem interpolation_through {A B : FixedCap S} (word : A.types = B.types)
    (i : Fin A.profile.size) (x : ℝ) (bottom : A.profile.x i = x)
    (top : B.profile.x (FixedCap.recoordinationSlots word i) = x) :
    let p := FixedCap.interpolationDrawing word
    (p.input i).val = (p.output (FixedCap.recoordinationSlots word i)).val ∧
      ∀ y, p.drawing.x (p.input i).val y = x := by
  constructor
  · change i = (FixedCap.recoordinationSlots word).symm (FixedCap.recoordinationSlots word i)
    rw [OrderIso.symm_apply_apply]
  · intro y
    change (FixedCap.interpolationDrawing word).drawing.x i y = _
    rw [FixedCap.interpolation_x, bottom, top]
    unfold interpolate
    ring

/-- The two splices retain the same wire from the lower cut to the upper cut. -/
theorem binary_through (e : S.Edge) {a b c d : O} (src : S.source e = [a, b]) (tgt : S.target e = [c, d])
    (Q : FixedCap S) {A B : FixedCap S} (input : A.types = [a, b] ++ Q.types)
    (output : [c, d] ++ Q.types = B.types) (j : Fin Q.profile.size)
    (bottom : A.profile.x (FixedCap.binaryThroughSlot a b Q input j) = ActiveStrip.right.place (Q.profile.x j))
    (top : B.profile.x (FixedCap.binaryThroughSlot c d Q output.symm j) = ActiveStrip.right.place (Q.profile.x j)) :
    let p := FixedCap.binaryLayer e src tgt Q input output
    let wi := (p.input (FixedCap.binaryThroughSlot a b Q input j)).val
    wi = (p.output (FixedCap.binaryThroughSlot c d Q output.symm j)).val ∧
      ∀ y, p.drawing.x wi y = ActiveStrip.right.place (Q.profile.x j) := by
  let L := binaryCap S a b
  let R := binaryCap S c d
  let box := binaryBox e src tgt
  let middle := ActiveStrip.left.placeDrawing (a := L) (b := R) box Q
  let lowerWord := input.trans (FixedCap.binary_beside_types a b Q).symm
  let upperWord := (FixedCap.binary_beside_types c d Q).trans output
  let enter := FixedCap.interpolationDrawing (a := A) (b := L.beside Q) lowerWord
  let leave := FixedCap.interpolationDrawing (a := R.beside Q) (b := B) upperWord
  let x := ActiveStrip.right.place (Q.profile.x j)
  let iL := (ActiveStrip.left.capSlots L Q).symm (.inr j)
  let iR := (ActiveStrip.left.capSlots R Q).symm (.inr j)
  let iA := FixedCap.binaryThroughSlot a b Q input j
  let iB := FixedCap.binaryThroughSlot c d Q output.symm j
  have lowerSlot : FixedCap.recoordinationSlots lowerWord iA = iL := by
    change (FixedCap.recoordinationSlots lowerWord) ((FixedCap.recoordinationSlots lowerWord).symm iL) = iL
    exact OrderIso.apply_symm_apply _ _
  have upperSlot : FixedCap.recoordinationSlots upperWord iR = iB := Fin.ext rfl
  have low := interpolation_through lowerWord iA x bottom (by
    rw [lowerSlot]
    exact ActiveStrip.left.idle_slot_x L Q j)
  have high := interpolation_through upperWord iR x (ActiveStrip.left.idle_slot_x R Q j) (by
    rw [upperSlot]
    exact top)
  rw [lowerSlot] at low
  rw [upperSlot] at high
  have midId : (middle.input iL).val = (middle.output iR).val :=
    (ActiveStrip.left.input_idle (a := L) (b := R) box Q j).trans
      (ActiveStrip.left.output_idle (a := L) (b := R) box Q j).symm
  have midX (y : ℝ) : middle.drawing.x (middle.input iL).val y = x := by
    change (ActiveStrip.left.placeDrawing (a := L) (b := R) box Q).drawing.x
      ((ActiveStrip.left.placeDrawing (a := L) (b := R) box Q).input iL).val y = x
    rw [ActiveStrip.left.input_idle (a := L) (b := R) box Q j]
    exact ActiveStrip.left.idle_x (a := L) (b := R) box Q j y
  have stitched := middle.thenDo_straight_through leave iL iR iB x midId high.1 midX high.2
  exact enter.thenDo_straight_through (middle.thenDo leave) iA iL iB x low.1 stitched.1 low.2 stitched.2

end Silmaril.RuntimeWires.Proofs.PositionedRuntime
