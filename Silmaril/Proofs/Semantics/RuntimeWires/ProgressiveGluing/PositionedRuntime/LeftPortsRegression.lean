module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftWord.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.PositionedRuntime.LeftPortsRegression

open CategoryTheory Presentation ProgressiveGraph

private abbrev system : EffectfulPolygraph where
  Obj := Fin 4
  pure := Signature.empty (Fin 4)
  effect := { Edge := Unit, source := fun _ => [1], target := fun _ => [2] }

private abbrev S := signature system

private def source : FixedRuntimeCap system := ⟨binaryCap S none (some 1), [1], rfl⟩
private def target : FixedRuntimeCap system := ⟨binaryCap S none (some 2), [2], rfl⟩

private def effectDrawing : FixedDrawing S source.cap.profile target.cap.profile :=
  binaryBox (S := S) (Edge.effect (G := system) ()) rfl rfl

private def singleContact (label : Fin 4) (x : ℝ) (inside : x ∈ Set.Ioo 0 1) : FixedCap S where
  profile :=
    { size := 1
      label _ := some label
      x _ := x
      ordered := fun {_ _} lt => (lt.ne (Subsingleton.elim _ _)).elim }
  inside _ := inside

private def idle := singleContact 0 (1 / 3) (by norm_num [Set.mem_Ioo])
private def lowerThrough := singleContact 1 (2 / 3) (by norm_num [Set.mem_Ioo])
private def upperThrough := singleContact 2 (2 / 3) (by norm_num [Set.mem_Ioo])

private def outerCap (upper : Bool) : FixedCap S where
  profile :=
    { size := 3
      label i := if i.val = 0 then none else if i.val = 1 then some 0 else some (if upper then 2 else 1)
      x i := if i.val = 0 then (if upper then 1 / 4 else 1 / 5)
        else if i.val = 1 then (if upper then 3 / 5 else 2 / 5) else 5 / 6
      ordered := by
        intro i j lt
        cases upper <;> fin_cases i <;> fin_cases j <;> norm_num at * }
  inside i := by cases upper <;> fin_cases i <;> norm_num [Set.mem_Ioo]

private abbrev bottomCap := source.leftBoundary 0 (outerCap false) rfl
private abbrev topCap := target.leftBoundary 0 (outerCap true) rfl

private def decorated : FixedDrawing S bottomCap.cap.profile topCap.cap.profile :=
  FixedRuntimeCap.placeLeftDrawing (X := source) (Y := target) 0 idle lowerThrough upperThrough
    rfl rfl rfl (A := outerCap false) (B := outerCap true) rfl rfl effectDrawing

private abbrev lowerWord : (idle.beside source.cap).types = [some 0, none] ++ lowerThrough.types :=
  source.leftPlaced_types 0 idle rfl

private abbrev upperWord : (idle.beside target.cap).types = [some 0, none] ++ upperThrough.types :=
  target.leftPlaced_types 0 idle rfl

/-- The lower crossing leaves the active input at slot two throughout. -/
example :
    let p := source.enterLeft 0 idle lowerThrough rfl rfl (A := outerCap false) rfl
    (p.input (2 : Fin 3)).val = (p.output (2 : Fin 3)).val ∧ ∀ y, p.drawing.x (p.input (2 : Fin 3)).val y = 5 / 6 := by
  have i : FixedCap.binaryThroughSlot none (some 0) lowerThrough (A := outerCap false) rfl (0 : Fin 1) = (2 : Fin 3) :=
    Fin.ext (FixedCap.binaryThroughSlot_val ..)
  have j : FixedCap.binaryThroughSlot (some 0) none lowerThrough lowerWord (0 : Fin 1) = (2 : Fin 3) :=
    Fin.ext (FixedCap.binaryThroughSlot_val ..)
  have h := FixedCap.binaryLayer_straight_through (S := S) (Edge.moveRight (G := system) 0) rfl rfl lowerThrough
    (A := outerCap false) (B := idle.beside source.cap) rfl lowerWord.symm (0 : Fin 1)
    (by
      rw [i]
      change (5 / 6 : ℝ) = (1 + 2 / 3) / 2
      norm_num)
    (by
      rw [j]
      rfl)
  dsimp only at h
  rw [i, j] at h
  exact ⟨h.1, fun y => (h.2 y).trans (by change ((1 + 2 / 3) / 2 : ℝ) = 5 / 6; norm_num)⟩

/-- The reverse crossing likewise leaves the differently typed output at slot two. -/
example :
    let p := target.leaveLeft 0 idle upperThrough rfl rfl (B := outerCap true) rfl
    (p.input (2 : Fin 3)).val = (p.output (2 : Fin 3)).val ∧ ∀ y, p.drawing.x (p.input (2 : Fin 3)).val y = 5 / 6 := by
  have i : FixedCap.binaryThroughSlot (some 0) none upperThrough upperWord (0 : Fin 1) = (2 : Fin 3) :=
    Fin.ext (FixedCap.binaryThroughSlot_val ..)
  have j : FixedCap.binaryThroughSlot none (some 0) upperThrough (A := outerCap true) rfl (0 : Fin 1) = (2 : Fin 3) :=
    Fin.ext (FixedCap.binaryThroughSlot_val ..)
  have h := FixedCap.binaryLayer_straight_through (S := S) (Edge.moveLeft (G := system) 0) rfl rfl upperThrough
    (A := idle.beside target.cap) (B := outerCap true) upperWord rfl (0 : Fin 1)
    (by rw [i]; rfl)
    (by
      rw [j]
      change (5 / 6 : ℝ) = (1 + 2 / 3) / 2
      norm_num)
  dsimp only at h
  rw [i, j] at h
  exact ⟨h.1, fun y => (h.2 y).trans (by change ((1 + 2 / 3) / 2 : ℝ) = 5 / 6; norm_num)⟩

private theorem read_effect :
    (FixedRuntimeCap.toComputations system).map (X := source) (Y := target)
      (FixedRuntimeCap.ofDrawing effectDrawing) = Computations.effect (G := system) () := by
  let e := Edge.effect (G := system) ()
  have count : effectDrawing.vertices = 1 := binaryBox_vertices (S := S) e rfl rfl
  let v : Fin effectDrawing.vertices := (0 : Fin 1).cast count.symm
  have only (j : Fin effectDrawing.vertices) : j = v :=
    (finCongr count).injective (Subsingleton.elim _ _)
  have h := FixedRuntimeCap.map_effect (X := source) (Y := target) () effectDrawing v only
    (binaryBox_generator (S := S) e rfl rfl v) (fun w => binaryBox_noThrough (S := S) e rfl rfl w v) rfl rfl
  refine h.trans ?_
  change 𝟙 source.computation ≫ Computations.effect (G := system) () ≫ 𝟙 target.computation = _
  erw [Category.id_comp, Category.comp_id]

/-- Actual gluing of a forward crossing, a value-changing effect beside an
idle strand, and the reverse crossing, with distinct outer cap coordinates. -/
example :
    (FixedRuntimeCap.toComputations system).map (X := bottomCap) (Y := topCap)
      (FixedRuntimeCap.ofDrawing decorated) =
    (Computations.whiskerLeft (Computations.mk (G := system) [0])).map (Computations.effect (G := system) ()) := by
  have h := FixedRuntimeCap.toComputations_placeLeft (X := source) (Y := target)
    0 idle lowerThrough upperThrough rfl rfl rfl
    (A := outerCap false) (B := outerCap true) rfl rfl effectDrawing
  exact h.trans (congrArg (Computations.whiskerLeft (Computations.mk (G := system) [0])).map read_effect)

private def nextIdle := singleContact 3 (1 / 4) (by norm_num [Set.mem_Ioo])

private def nextThrough (upper : Bool) : FixedCap S where
  profile :=
    { size := 2
      label i := if i.val = 0 then some 0 else some (if upper then 2 else 1)
      x i := if i.val = 0 then (if upper then 3 / 5 else 2 / 5) else 5 / 6
      ordered := by
        intro i j lt
        cases upper <;> fin_cases i <;> fin_cases j <;> norm_num at * }
  inside i := by cases upper <;> fin_cases i <;> norm_num [Set.mem_Ioo]

private def twoIdleCap (upper : Bool) : FixedCap S where
  profile :=
    { size := 4
      label i := if i.val = 0 then none else if i.val = 1 then some 3
        else if i.val = 2 then some 0 else some (if upper then 2 else 1)
      x i := if i.val = 0 then (if upper then 1 / 7 else 1 / 8)
        else if i.val = 1 then (if upper then 1 / 2 else 1 / 3)
        else if i.val = 2 then (if upper then 4 / 5 else 7 / 10) else 11 / 12
      ordered := by
        intro i j lt
        cases upper <;> fin_cases i <;> fin_cases j <;> norm_num at * }
  inside i := by cases upper <;> fin_cases i <;> norm_num [Set.mem_Ioo]

private theorem next_outer_coordinate (upper : Bool) (j : Fin 2) :
    (twoIdleCap upper).profile.x (j.natAdd 2) = ActiveStrip.right.place ((nextThrough upper).profile.x j) := by
  cases upper <;> fin_cases j
  · change (7 / 10 : ℝ) = (1 + 2 / 5) / 2
    norm_num
  · change (11 / 12 : ℝ) = (1 + 5 / 6) / 2
    norm_num
  · change (4 / 5 : ℝ) = (1 + 3 / 5) / 2
    norm_num
  · change (11 / 12 : ℝ) = (1 + 5 / 6) / 2
    norm_num

/-- The first idle value and the active input keep their wire IDs and full
straight tracks through the additional lower crossing. -/
example (j : Fin 2) :
    let p := bottomCap.enterLeft 3 nextIdle (nextThrough false) rfl rfl (A := twoIdleCap false) rfl
    (p.input (j.natAdd 2)).val = (p.output (j.natAdd 2)).val ∧
      ∀ y, p.drawing.x (p.input (j.natAdd 2)).val y = ActiveStrip.right.place ((nextThrough false).profile.x j) := by
  let Q := nextThrough false
  let A := twoIdleCap false
  let B := nextIdle.beside bottomCap.cap
  have input : A.types = [none, some 3] ++ Q.types := rfl
  have output : [some 3, none] ++ Q.types = B.types := rfl
  have lo : FixedCap.binaryThroughSlot none (some 3) Q input j = j.natAdd 2 :=
    Fin.ext (FixedCap.binaryThroughSlot_val ..)
  have hi : FixedCap.binaryThroughSlot (some 3) none Q output.symm j = j.natAdd 2 :=
    Fin.ext (FixedCap.binaryThroughSlot_val ..)
  have h := FixedCap.binaryLayer_straight_through (S := S) (Edge.moveRight (G := system) 3) rfl rfl Q
    input output j (by rw [lo]; exact next_outer_coordinate false j) (by rw [hi]; fin_cases j <;> rfl)
  dsimp only at h
  rw [lo, hi] at h
  exact h

/-- The earlier idle value and the active output likewise survive the
additional reverse crossing. -/
example (j : Fin 2) :
    let p := topCap.leaveLeft 3 nextIdle (nextThrough true) rfl rfl (B := twoIdleCap true) rfl
    (p.input (j.natAdd 2)).val = (p.output (j.natAdd 2)).val ∧
      ∀ y, p.drawing.x (p.input (j.natAdd 2)).val y = ActiveStrip.right.place ((nextThrough true).profile.x j) := by
  let Q := nextThrough true
  let A := nextIdle.beside topCap.cap
  let B := twoIdleCap true
  have input : A.types = [some 3, none] ++ Q.types := rfl
  have output : [none, some 3] ++ Q.types = B.types := rfl
  have lo : FixedCap.binaryThroughSlot (some 3) none Q input j = j.natAdd 2 :=
    Fin.ext (FixedCap.binaryThroughSlot_val ..)
  have hi : FixedCap.binaryThroughSlot none (some 3) Q output.symm j = j.natAdd 2 :=
    Fin.ext (FixedCap.binaryThroughSlot_val ..)
  have h := FixedCap.binaryLayer_straight_through (S := S) (Edge.moveLeft (G := system) 3) rfl rfl Q
    input output j (by rw [lo]; fin_cases j <;> rfl) (by rw [hi]; exact next_outer_coordinate true j)
  dsimp only at h
  rw [lo, hi] at h
  exact h

private def firstPlacement : FixedRuntimeCap.LeftPlacement source target [0] (outerCap false) (outerCap true) :=
  .cons (.nil (X := source) (Y := target)) 0 idle lowerThrough upperThrough rfl rfl rfl rfl rfl

private def secondPlacement : FixedRuntimeCap.LeftPlacement source target [3, 0] (twoIdleCap false) (twoIdleCap true) :=
  .cons firstPlacement 3 nextIdle (nextThrough false) (nextThrough true) rfl rfl rfl rfl rfl

private def twiceDecorated := secondPlacement.drawing effectDrawing

example :
    (FixedRuntimeCap.toComputations system).map (X := secondPlacement.source) (Y := secondPlacement.target)
      (FixedRuntimeCap.ofDrawing twiceDecorated) =
    (Computations.whiskerLeft (Computations.mk (G := system) [3, 0])).map (Computations.effect (G := system) ()) :=
  (secondPlacement.toComputations_drawing effectDrawing).trans
    (congrArg (Computations.whiskerLeft (Computations.mk (G := system) [3, 0])).map read_effect)

/-- Independently read rows show the runtime crossing `3`, then `0`,
performing the effect, and returning through `0`, then `3`. The active
value is present as a through cell on the right of both crossing pairs. -/
example : twiceDecorated.readSheet.cells =
    [[.inr (.moveRight 3), .inl (some 0), .inl (some 1)],
     [.inl (some 3), .inr (.moveRight 0), .inl (some 1)],
     [.inl (some 3), .inl (some 0), .inr (.effect ())],
     [.inl (some 3), .inr (.moveLeft 0), .inl (some 2)],
     [.inr (.moveLeft 3), .inl (some 0), .inl (some 2)]] := by
  change (FixedRuntimeCap.placeLeftDrawing (X := bottomCap) (Y := topCap)
    3 nextIdle (nextThrough false) (nextThrough true) rfl rfl rfl
    (A := twoIdleCap false) (B := twoIdleCap true) rfl rfl decorated).readSheet.cells = _
  erw [FixedRuntimeCap.placeLeftDrawing_cells]
  unfold decorated
  erw [FixedRuntimeCap.placeLeftDrawing_cells]
  unfold effectDrawing
  erw [binaryBox_cells]
  rfl

end Silmaril.RuntimeWires.Proofs.PositionedRuntime.LeftPortsRegression
