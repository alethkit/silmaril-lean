module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.PositionedRuntime.LeftPortsRegression

open CategoryTheory Presentation ProgressiveGraph

private abbrev system : EffectfulPolygraph where
  Obj := Fin 3
  pure := Signature.empty (Fin 3)
  effect := { Edge := Unit, source := fun _ => [1], target := fun _ => [2] }

private abbrev S := signature system

private def source : FixedRuntimeCap system := ⟨binaryCap S none (some 1), [1], rfl⟩
private def target : FixedRuntimeCap system := ⟨binaryCap S none (some 2), [2], rfl⟩

private def effectDrawing : FixedDrawing S source.cap.profile target.cap.profile :=
  binaryBox (S := S) (Edge.effect (G := system) ()) rfl rfl

private def singleContact (label : Fin 3) (x : ℝ) (inside : x ∈ Set.Ioo 0 1) : FixedCap S where
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

end Silmaril.RuntimeWires.Proofs.PositionedRuntime.LeftPortsRegression
