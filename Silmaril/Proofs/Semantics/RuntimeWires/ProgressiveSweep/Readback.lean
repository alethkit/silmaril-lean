module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSweep.Sweep
import Mathlib.Data.Finset.Max

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSweep

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W}
variable (s : d.Sweep) (w : Fin W)

private theorem wireCuts_mem (i : Fin (V + 1)) : i ∈ s.wireCuts w ↔ w ∈ s.wires i := by
  simp [Diagram.Sweep.wireCuts]

theorem wireCuts_nonempty : (s.wireCuts w).Nonempty := by
  obtain ⟨i, hi⟩ := some_cut s w
  exact ⟨i, (wireCuts_mem s w i).mpr hi⟩

theorem first_index :
    ((s.wireCuts w).min' (wireCuts_nonempty s w)).castSucc = d.startIndex w := by
  have precedes := endpoint_indices d w
  change (d.startIndex w).val < (d.finishIndex w).val at precedes
  let i : Fin (V + 1) := ⟨(d.startIndex w).val, by have := (d.finishIndex w).isLt; omega⟩
  have hm : i ∈ s.wireCuts w :=
    (wireCuts_mem s w i).mpr ((wire_span s i w).mpr ⟨le_rfl, precedes⟩)
  have hlow := (s.wireCuts w).min'_le i hm
  have hhigh := ((wire_span s _ w).mp ((wireCuts_mem s w _).mp
    ((s.wireCuts w).min'_mem (wireCuts_nonempty s w)))).1
  exact Fin.ext (le_antisymm hlow hhigh)

theorem last_index :
    ((s.wireCuts w).max' (wireCuts_nonempty s w)).succ = d.finishIndex w := by
  have precedes := endpoint_indices d w
  change (d.startIndex w).val < (d.finishIndex w).val at precedes
  let i : Fin (V + 1) := ⟨(d.finishIndex w).val - 1, by have := (d.finishIndex w).isLt; omega⟩
  have hm : i ∈ s.wireCuts w := by
    apply (wireCuts_mem s w i).mpr
    apply (wire_span s i w).mpr
    dsimp [i]
    omega
  have hlo := (s.wireCuts w).le_max' i hm
  have hhi := ((wire_span s _ w).mp ((wireCuts_mem s w _).mp
    ((s.wireCuts w).max'_mem (wireCuts_nonempty s w)))).2
  change (d.finishIndex w).val - 1 ≤ ((s.wireCuts w).max' (wireCuts_nonempty s w)).val at hlo
  apply Fin.ext
  change ((s.wireCuts w).max' (wireCuts_nonempty s w)).val + 1 = (d.finishIndex w).val
  omega

private theorem vertexAt_vertexIndex (v : Fin V) : d.vertexAt (d.vertexIndex v) = some v := by
  simp [Diagram.vertexAt, Diagram.vertexIndex]

theorem vertexAt_start (d : Diagram S V W) (w : Fin W) :
    d.vertexAt (d.startIndex w) = d.start w := by
  cases h : d.start w with
  | none => simp [Diagram.startIndex, Diagram.vertexAt, h]
  | some v => simpa [Diagram.startIndex, h] using vertexAt_vertexIndex (d := d) v

theorem vertexAt_finish (d : Diagram S V W) (w : Fin W) :
    d.vertexAt (d.finishIndex w) = d.finish w := by
  cases h : d.finish w with
  | none =>
    rw [Diagram.finishIndex, h]
    change d.vertexAt (Fin.last (V + 1)) = none
    rw [← Fin.succ_last]
    simp only [Diagram.vertexAt, Fin.cases_succ, Fin.lastCases_last]
  | some v => simpa [Diagram.finishIndex, h] using vertexAt_vertexIndex (d := d) v

end Silmaril.RuntimeWires.Proofs.ProgressiveSweep
