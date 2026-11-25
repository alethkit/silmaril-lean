module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Collar
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing.CollarRegression

open ProgressiveGraph

private abbrev signature : Signature Bool where
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

private noncomputable def leftX (i : Fin 2) : ℝ := if i = 0 then 1 / 6 else 1 / 2
private noncomputable def rightX (i : Fin 2) : ℝ := if i = 0 then 5 / 6 else 1 / 3

private noncomputable def operand (side : Bool) : CollarSpec Bool 2 where
  label i := if side then decide (i = 0) else decide (i = 1)
  bottom := if side then rightX else leftX
  top := if side then rightX else leftX
  bottom_inside := by intro i; cases side <;> fin_cases i <;> norm_num [leftX, rightX, Set.mem_Ioo]
  top_inside := by intro i; cases side <;> fin_cases i <;> norm_num [leftX, rightX, Set.mem_Ioo]
  bottom_injective := by
    intro i j h
    cases side <;> fin_cases i <;> fin_cases j <;> norm_num [leftX, rightX] at *
  order _ _ := Iff.rfl

private noncomputable def lower := (operand false).drawing signature
private noncomputable def upper := (operand true).drawing signature

private noncomputable def leftCap (i : Fin 2) : Diagram.PartialVerticalMatch.Contact lower :=
  ⟨i, (operand false).drawing_finish i⟩

private noncomputable def rightCap (i : Fin 2) : {w : Fin 2 // upper.start w = none} :=
  ⟨i, (operand true).drawing_start i⟩

private def swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

private noncomputable def matched : lower.OrderedVerticalMatch upper where
  contact :=
    { toFun := fun w => rightCap (swap w.val)
      invFun := fun w => leftCap (swap w.val)
      left_inv := fun _ => Subtype.ext (Equiv.swap_apply_self _ _ _)
      right_inv := fun _ => Subtype.ext (Equiv.swap_apply_self _ _ _) }
  label w := by
    change ((operand false).drawing signature).label w.val =
      ((operand true).drawing signature).label (swap w.val)
    rw [CollarSpec.drawing_label, CollarSpec.drawing_label]
    obtain ⟨w, _⟩ := w
    fin_cases w <;> rfl
  order a b := by
    change ((operand false).drawing signature).x a.val 1 < ((operand false).drawing signature).x b.val 1 ↔
      ((operand true).drawing signature).x (swap a.val) 0 < ((operand true).drawing signature).x (swap b.val) 0
    rw [CollarSpec.drawing_top, CollarSpec.drawing_top, CollarSpec.drawing_bottom, CollarSpec.drawing_bottom]
    obtain ⟨a, _⟩ := a
    obtain ⟨b, _⟩ := b
    have inv₀ : swap 0 = 1 := Equiv.swap_apply_left _ _
    have inv₁ : swap 1 = 0 := Equiv.swap_apply_right _ _
    fin_cases a <;> fin_cases b <;> norm_num [operand, leftX, rightX, inv₀, inv₁]

private noncomputable def first := Diagram.OrderedVerticalMatch.collarIndex lower (leftCap 0)
private noncomputable def second := Diagram.OrderedVerticalMatch.collarIndex lower (leftCap 1)

private theorem first_x (y : ℝ) : matched.collar.x first y = interpolate (1 / 6) (1 / 3) y := by
  rw [first, matched.collar_x]
  change interpolate ((operand false).drawing signature |>.x 0 1)
    ((operand true).drawing signature |>.x (swap 0) 0) y = _
  rw [CollarSpec.drawing_top, CollarSpec.drawing_bottom, show swap 0 = 1 from Equiv.swap_apply_left _ _]
  rfl

private theorem second_x (y : ℝ) : matched.collar.x second y = interpolate (1 / 2) (5 / 6) y := by
  rw [second, matched.collar_x]
  change interpolate ((operand false).drawing signature |>.x 1 1)
    ((operand true).drawing signature |>.x (swap 1) 0) y = _
  rw [CollarSpec.drawing_top, CollarSpec.drawing_bottom, show swap 1 = 0 from Equiv.swap_apply_right _ _]
  rfl

/-- The endpoint spacings differ. Both strands retain their order and
interpolate to these exact points at the collar midpoint. -/
example : (matched.collar.x first (1 / 2), matched.collar.x second (1 / 2)) = (1 / 4, 2 / 3) := by
  rw [first_x, second_x]
  norm_num [interpolate]

/-- The first strand reaches the same midpoint after placement in the
actual composite collar slab. -/
example : matched.glue.x (matched.upperJoin.upperId (matched.contact (leftCap 0)).val) (3 / 8) = 1 / 4 := by
  rw [matched.glue_x_in_collar (leftCap 0) (by norm_num [Set.mem_Icc]),
    show (4 * (3 / 8 : ℝ) - 1) = 1 / 2 by norm_num, ← matched.collar_x]
  change matched.collar.x first (1 / 2) = _
  rw [first_x]
  norm_num [interpolate]

private noncomputable def collarRead := matched.collar.layerSweep

private theorem lowerOrdered :
    ([leftCap 0, leftCap 1]).Pairwise (fun a b => lower.x a.val 1 < lower.x b.val 1) := by
  simp [List.pairwise_cons]
  change ((operand false).drawing signature).x 0 1 < ((operand false).drawing signature).x 1 1
  rw [CollarSpec.drawing_top, CollarSpec.drawing_top]
  norm_num [operand, leftX]

private theorem allContacts (w : Diagram.PartialVerticalMatch.Contact lower) : w ∈ [leftCap 0, leftCap 1] := by
  obtain ⟨i, h⟩ := w
  fin_cases i
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

example : collarRead.word 0 = [false, true] := by
  have active := (matched.collar.level_gap_regular (collarRead.cuts.in_gap 0)).1
  have ids := Diagram.ordered_cut_unique (collarRead.ordered 0)
    (matched.collar_ordered_cut allContacts lowerOrdered active)
  rw [Diagram.LayerSweep.word, ids]
  change [matched.collar.label first, matched.collar.label second] = _
  rw [first, second, matched.collar_label, matched.collar_label]
  exact congrArg₂ List.cons ((operand false).drawing_label 0) (congrArg List.singleton ((operand false).drawing_label 1))

example : collarRead.sheet.reindex rfl (matched.collar_word collarRead) = Sliced.Sheet.empty (collarRead.word 0) :=
  matched.collar_identity collarRead

private noncomputable def lowerRead := lower.layerSweep
private noncomputable def upperRead := upper.layerSweep
private noncomputable def fullRead := matched.glue.layerSweep

example :
    fullRead.sheet.reindex (matched.sweep_first_word lowerRead fullRead) (matched.sweep_last_word upperRead fullRead) =
      lowerRead.sheet.thenDo (upperRead.sheet.reindex (matched.sweep_join_word lowerRead upperRead) rfl) :=
  matched.sweep_concat lowerRead upperRead fullRead

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing.CollarRegression
