module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.BinaryBox.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.PositionedRuntime.BinaryBox

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

private def gateStart (i : Fin 4) : Option (Fin 1) :=
  if i.val < 2 then none else some 0

private def gateFinish (i : Fin 4) : Option (Fin 1) :=
  if i.val < 2 then some 0 else none

private def gateX (i : Fin 4) (y : ℝ) : ℝ :=
  if i.val = 0 ∨ i.val = 3 then 1 / 6 + y / 2 else 2 / 3 - y / 2

private def gateLabel (a b c d : O) (i : Fin 4) : O :=
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d

private def gateWire (i : Fin 4) : ProgressiveGraph.Wire
    (endpointHeight (fun _ => 1 / 2) 0 (gateStart i))
    (endpointHeight (fun _ => 1 / 2) 1 (gateFinish i)) where
  x := gateX i
  increasing := by fin_cases i <;> norm_num [gateStart, gateFinish, endpointHeight]
  continuous := by
    unfold gateX
    split
    · exact (continuous_const.add (continuous_id.div_const _)).continuousOn
    · exact (continuous_const.sub (continuous_id.div_const _)).continuousOn
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    unfold gateX
    split <;> ring

private def gateIn {n : ℕ} (size : n = 2) (i : Fin n) : Fin 4 := i.castLE (by omega)

private def gateOut {n : ℕ} (size : n = 2) (i : Fin n) : Fin 4 :=
  ⟨i.val + 2, by have bound := i.isLt; omega⟩

variable (e : S.Edge) {a b c d : O} (inTypes : S.source e = [a, b])
  (outTypes : S.target e = [c, d])

private abbrev inSize : (S.source e).length = 2 := congrArg List.length inTypes
private abbrev outSize : (S.target e).length = 2 := congrArg List.length outTypes

/-- The four affine arms meet only at the point vertex. -/
private def gate : ProgressiveGraph.Diagram S 1 4 .point where
  vertexX _ := 5 / 12
  vertexHeight _ := 1 / 2
  vertex_inside _ := by norm_num [Set.mem_Ioo]
  vertex_separation := fun {_ _} _ => Subsingleton.elim _ _
  generator _ := e
  label := gateLabel a b c d
  start := gateStart
  finish := gateFinish
  wire := gateWire
  wire_inside := by
    intro i y h
    fin_cases i <;> norm_num [gateWire, gateX, gateStart, gateFinish, endpointHeight, Set.mem_Ioo] at *
    all_goals constructor <;> linarith [h.1, h.2]
  start_attached i _ _ := by fin_cases i <;> norm_num [gateWire, gateX]
  finish_attached i _ _ := by fin_cases i <;> norm_num [gateWire, gateX]
  separated := by
    intro i j ne y hi hj
    fin_cases i <;> fin_cases j <;>
      norm_num [gateWire, gateX, gateStart, gateFinish, endpointHeight, Set.mem_Ioo, Set.mem_Icc] at *
    all_goals linarith [hi.1, hi.2, hj.1, hj.2]
  avoids_vertex i _ h := by
    fin_cases i <;> norm_num [gateStart, gateFinish, endpointHeight, Set.mem_Ioo] at h
  input_boundary_separated := by
    intro i j ne hi hj
    fin_cases i <;> fin_cases j <;> norm_num [gateStart, gateWire, gateX] at *
  output_boundary_separated := by
    intro i j ne hi hj
    fin_cases i <;> fin_cases j <;> norm_num [gateFinish, gateWire, gateX] at *
  input _ := gateIn (inSize e inTypes)
  output _ := gateOut (outSize e outTypes)
  input_exact := by
    intro v i
    obtain rfl : v = 0 := Subsingleton.elim _ _
    change gateFinish i = some 0 ↔ ∃ j, gateIn (inSize e inTypes) j = i
    constructor
    · intro h
      have inside : i.val < 2 := by
        unfold gateFinish at h
        split at h
        · assumption
        · cases h
      exact ⟨⟨i.val, (inSize e inTypes).symm ▸ inside⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩
      have inside : j.val < 2 := (inSize e inTypes) ▸ j.isLt
      simp [gateFinish, gateIn, inside]
  output_exact := by
    intro v i
    obtain rfl : v = 0 := Subsingleton.elim _ _
    change gateStart i = some 0 ↔ ∃ j, gateOut (outSize e outTypes) j = i
    constructor
    · intro h
      have lower : 2 ≤ i.val := by
        unfold gateStart at h
        split at h
        · cases h
        · omega
      have upper := i.isLt
      refine ⟨⟨i.val - 2, by rw [outSize e outTypes]; omega⟩, Fin.ext ?_⟩
      change i.val - 2 + 2 = i.val
      omega
    · rintro ⟨j, rfl⟩
      simp [gateStart, gateOut]
  input_types _ := by
    refine Eq.trans ?_ inTypes.symm
    rw [List.map_ofFn, List.ofFn_congr (inSize e inTypes)]
    rfl
  output_types _ := by
    refine Eq.trans ?_ outTypes.symm
    rw [List.map_ofFn, List.ofFn_congr (outSize e outTypes)]
    rfl
  input_order := by
    intro v i j less y hi hj hy
    have vi : i.val < 2 := (inSize e inTypes) ▸ i.isLt
    have vj : j.val < 2 := (inSize e inTypes) ▸ j.isLt
    have ei : i.val = 0 := by omega
    have ej : j.val = 1 := by omega
    norm_num [gateIn, gateWire, gateX, ei, ej] at *
    linarith
  output_order := by
    intro v i j less y hy hi hj
    have vi : i.val < 2 := (outSize e outTypes) ▸ i.isLt
    have vj : j.val < 2 := (outSize e outTypes) ▸ j.isLt
    have ei : i.val = 0 := by omega
    have ej : j.val = 1 := by omega
    norm_num [gateOut, gateWire, gateX, ei, ej] at *
    linarith

private def lowerSlots : Fin 2 ≃ {w : Fin 4 // (gate e inTypes outTypes).start w = none} where
  toFun i := ⟨i.castAdd 2, by
    change gateStart (i.castAdd 2) = none
    simp [gateStart, i.isLt]⟩
  invFun w := ⟨w.val.val, by
    have hw := w.property
    change gateStart w.val = none at hw
    simpa [gateStart] using hw⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Subtype.ext (Fin.ext rfl)

private def upperSlots : Fin 2 ≃ {w : Fin 4 // (gate e inTypes outTypes).finish w = none} where
  toFun i := ⟨i.natAdd 2, by
    change gateFinish (i.natAdd 2) = none
    simp [gateFinish]⟩
  invFun w := ⟨w.val.val - 2, by have hw := w.val.isLt; omega⟩
  left_inv i := by apply Fin.ext; change 2 + i.val - 2 = i.val; omega
  right_inv w := by
    apply Subtype.ext
    apply Fin.ext
    have hw := w.property
    change gateFinish w.val = none at hw
    have bound : 2 ≤ w.val.val := by
      unfold gateFinish at hw
      split at hw
      · cases hw
      · omega
    change 2 + (w.val.val - 2) = w.val.val
    omega


def box : FixedDrawing S (binaryCap S a b).profile (binaryCap S c d).profile where
  vertices := 1
  wires := 4
  drawing := gate e inTypes outTypes
  input := lowerSlots e inTypes outTypes
  output := upperSlots e inTypes outTypes
  input_label i := by fin_cases i <;> rfl
  output_label i := by fin_cases i <;> rfl
  input_x i := by
    fin_cases i
    · change (1 / 6 : ℝ) + 0 / 2 = 1 / 6
      norm_num
    · change (2 / 3 : ℝ) - 0 / 2 = 2 / 3
      norm_num
  output_x i := by
    fin_cases i
    · change (2 / 3 : ℝ) - 1 / 2 = 1 / 6
      norm_num
    · change (1 / 6 : ℝ) + 1 / 2 = 2 / 3
      norm_num

theorem box_noThrough (i : Fin (box e inTypes outTypes).wires)
    (j : Fin (box e inTypes outTypes).vertices) :
    ¬ (box e inTypes outTypes).drawing.crosses i ((box e inTypes outTypes).drawing.vertexHeight j) := by
  change ¬ (gate e inTypes outTypes).crosses i (1 / 2)
  fin_cases i <;> norm_num [Diagram.crosses, Diagram.lower, Diagram.upper, gate, gateStart,
    gateFinish, endpointHeight, Set.mem_Ioo]

theorem box_cells : (box e inTypes outTypes).readSheet.cells = [[.inr e]] := by
  let p := box e inTypes outTypes
  have h := p.readSheetAt_generator p.drawing.layerSweep e (0 : Fin 1)
    (fun j => Subsingleton.elim (α := Fin 1) j 0) rfl (fun i => box_noThrough e inTypes outTypes i (0 : Fin 1))
    (inTypes.trans (binaryCap_types S a b).symm) (outTypes.trans (binaryCap_types S c d).symm)
  change (p.readSheetAt p.drawing.layerSweep).cells = _
  rw [h]
  simp only [Sliced.Sheet.generator, Sliced.Sheet.cells_reindex, Sliced.Sheet.cells_cons,
    Sliced.Sheet.cells_empty, Sliced.Row.cells_box,
    show (Sliced.Row.empty (S := S)).cells = [] from Sliced.Row.cells_straight []]

end Silmaril.RuntimeWires.Proofs.PositionedRuntime.BinaryBox
