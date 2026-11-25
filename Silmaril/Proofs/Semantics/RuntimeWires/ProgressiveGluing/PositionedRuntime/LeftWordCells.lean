module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.PositionedRuntime

open Presentation ProgressiveGraph
open Sliced (Sheet)

universe u v

private theorem interpolation_cells {O : Type u} {S : Signature.{u,v} O} {A B : FixedCap S}
    (word : A.types = B.types) : (FixedCap.interpolationDrawing word).readSheet.cells = [] := by
  erw [FixedDrawing.readSheet_vertexFree _ rfl word, Sheet.cells_reindex, Sheet.cells_empty]

private theorem binaryLayer_cells {O : Type u} {S : Signature.{u,v} O}
    (e : S.Edge) {a b c d : O} (src : S.source e = [a, b]) (tgt : S.target e = [c, d])
    (Q : FixedCap S) {A B : FixedCap S} (input : A.types = [a, b] ++ Q.types)
    (output : [c, d] ++ Q.types = B.types) :
    (FixedCap.binaryLayer e src tgt Q input output).readSheet.cells =
      [.inr e :: Q.types.map Sum.inl] := by
  let L := binaryCap S a b
  let R := binaryCap S c d
  let p := binaryBox e src tgt
  let i := input.trans (FixedCap.binary_beside_types a b Q).symm
  let o := (FixedCap.binary_beside_types c d Q).trans output
  let placed := ActiveStrip.left.placeDrawing (a := L) (b := R) p Q
  change ((FixedCap.interpolationDrawing (a := A) (b := L.beside Q) i).thenDo
    (placed.thenDo (FixedCap.interpolationDrawing (a := R.beside Q) (b := B) o))).readSheet.cells = _
  erw [FixedDrawing.readSheet_thenDo, FixedDrawing.readSheet_thenDo, Sheet.cells_thenDo,
    Sheet.cells_thenDo, interpolation_cells i, interpolation_cells o, List.nil_append, List.append_nil]
  change (placed.readSheetAt placed.drawing.layerSweep).cells = _
  erw [ActiveStrip.readSheetAt_left (a := L) (b := R) p Q p.drawing.layerSweep placed.drawing.layerSweep,
    Sheet.cells_reindex, Sheet.cells_padRight]
  change p.readSheet.cells.map _ = _
  rw [binaryBox_cells]
  rfl

variable {G : EffectfulPolygraph.{u,v}} {X Y : FixedRuntimeCap G}

theorem place_left_cells (x : G.Obj) (idle lower upper : FixedCap (signature G))
    (idleTypes : idle.types = [some x]) (lowerTypes : lower.types = values X.word)
    (upperTypes : upper.types = values Y.word) {A B : FixedCap (signature G)}
    (input : A.types = none :: some x :: values X.word)
    (output : B.types = none :: some x :: values Y.word)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    (FixedRuntimeCap.placeLeftDrawing x idle lower upper idleTypes lowerTypes upperTypes
      input output p).readSheet.cells =
      [.inr (.moveRight x) :: (values X.word).map Sum.inl] ++
        p.readSheet.cells.map (.inl (some x) :: ·) ++
        [.inr (.moveLeft x) :: (values Y.word).map Sum.inl] := by
  let placed := ActiveStrip.right.placeDrawing (a := X.cap) (b := Y.cap) p idle
  have middle : placed.readSheet.cells = p.readSheet.cells.map (.inl (some x) :: ·) := by
    change (placed.readSheetAt placed.drawing.layerSweep).cells = _
    erw [ActiveStrip.readSheetAt_right (a := X.cap) (b := Y.cap) p idle p.drawing.layerSweep placed.drawing.layerSweep,
      Sheet.cells_reindex, Sheet.cells_padLeft, idleTypes]
    rfl
  have first := binaryLayer_cells (S := signature G) (Edge.moveRight x) rfl rfl lower
    (A := A) (B := idle.beside X.cap)
    (input.trans (congrArg ([none, some x] ++ ·) lowerTypes.symm))
    ((congrArg ([some x, none] ++ ·) lowerTypes).trans (X.leftPlaced_types x idle idleTypes).symm)
  have last := binaryLayer_cells (S := signature G) (Edge.moveLeft x) rfl rfl upper
    (A := idle.beside Y.cap) (B := B)
    ((Y.leftPlaced_types x idle idleTypes).trans (congrArg ([some x, none] ++ ·) upperTypes.symm))
    ((congrArg ([none, some x] ++ ·) upperTypes).trans output.symm)
  let enter := X.enterLeft x idle lower idleTypes lowerTypes input
  let leave := Y.leaveLeft x idle upper idleTypes upperTypes output
  change (enter.thenDo (placed.thenDo leave)).readSheet.cells = _
  erw [FixedDrawing.readSheet_thenDo enter (placed.thenDo leave), FixedDrawing.readSheet_thenDo placed leave,
    Sheet.cells_thenDo,
    Sheet.cells_thenDo, first, middle, last, lowerTypes, upperTypes]
  exact (List.append_assoc ..).symm

end Silmaril.RuntimeWires.Proofs.PositionedRuntime
