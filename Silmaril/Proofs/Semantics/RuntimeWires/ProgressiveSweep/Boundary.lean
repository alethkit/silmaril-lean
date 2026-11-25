module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSweep.Sweep

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSweep

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W}

theorem input_mem (s : d.Sweep) (w : Fin W) :
    w ∈ s.wires 0 ↔ d.start w = none := by
  rw [wire_span]
  have hf : 0 < (d.finishIndex w).val := (Nat.zero_le _).trans_lt (endpoint_indices d w)
  cases hw : d.start w <;> simp [Diagram.startIndex, Diagram.vertexIndex, hw, hf]

theorem output_mem (s : d.Sweep) (w : Fin W) :
    w ∈ s.wires (Fin.last V) ↔ d.finish w = none := by
  rw [wire_span]
  change (d.startIndex w).val ≤ V ∧ V < (d.finishIndex w).val ↔ _
  cases hw : d.finish w with
  | none =>
    have h : (d.startIndex w).val < V + 1 := by
      have he := endpoint_indices d w
      change (d.startIndex w).val < (d.finishIndex w).val at he
      simpa only [Diagram.finishIndex, hw, Option.elim_none, Fin.val_last] using he
    simp [Diagram.finishIndex, hw, Nat.lt_succ_iff.mp h]
  | some v =>
    have hv := (d.vertexOrder.symm v).isLt
    have hf : ¬ V < (d.finishIndex w).val := by
      simp only [Diagram.finishIndex, Diagram.vertexIndex, hw, Option.elim_some, Fin.val_succ,
        Fin.val_castSucc]
      omega
    simp [hf]

theorem input_boundary_order {kind : VertexSeparation} {d : Diagram S V W kind}
    {h : ℝ} {wires : List (Fin W)} (cut : d.OrderedCut h wires)
    (hh : 0 < h) (incident : ∀ w ∈ wires, d.start w = none) :
    wires.Pairwise (fun a b => d.x a 0 < d.x b 0) := by
  refine cut.ordered.imp_of_mem ?_
  intro a b ha hb hab
  have sta := incident a ha
  have stb := incident b hb
  have ha₀ : d.lower a = 0 := by simp [Diagram.lower, endpointHeight, sta]
  have hb₀ : d.lower b = 0 := by simp [Diagram.lower, endpointHeight, stb]
  have ha₁ := (cut.exact_wires a).mp ha
  have hb₁ := (cut.exact_wires b).mp hb
  have hne : a ≠ b := ne_of_apply_ne (fun w => d.x w h) (ne_of_lt hab)
  have bounds (y : ℝ) (hy : y ∈ Set.uIcc h 0) : 0 ≤ y ∧ y ≤ h := by
    simpa only [Set.uIcc_of_ge hh.le, Set.mem_Icc] using hy
  have covers (y : ℝ) (hy : y ∈ Set.uIcc h 0) : d.covers a y ∧ d.covers b y := by
    have hy' := bounds y hy
    exact ⟨⟨ha₀.symm ▸ hy'.1, hy'.2.trans ha₁.2.le⟩, hb₀.symm ▸ hy'.1,
      hy'.2.trans hb₁.2.le⟩
  refine Diagram.order_across covers (fun y hy => ?_) hab
  rcases eq_or_lt_of_le (bounds y hy).1 with hy' | hy'
  · rw [← hy']
    exact d.input_boundary_separated hne sta stb
  · have hlo : d.lower a < y := by rw [ha₀]; exact hy'
    exact d.separated hne ⟨hlo, (bounds y hy).2.trans_lt ha₁.2⟩ (covers y hy).2

theorem output_boundary_order {kind : VertexSeparation} {d : Diagram S V W kind}
    {h : ℝ} {wires : List (Fin W)} (cut : d.OrderedCut h wires)
    (hh : h < 1) (incident : ∀ w ∈ wires, d.finish w = none) :
    wires.Pairwise (fun a b => d.x a 1 < d.x b 1) := by
  refine cut.ordered.imp_of_mem ?_
  intro a b ha hb hab
  have fna := incident a ha
  have fnb := incident b hb
  have ha₁ : d.upper a = 1 := by simp [Diagram.upper, endpointHeight, fna]
  have hb₁ : d.upper b = 1 := by simp [Diagram.upper, endpointHeight, fnb]
  have ha₀ := (cut.exact_wires a).mp ha
  have hb₀ := (cut.exact_wires b).mp hb
  have hne : a ≠ b := ne_of_apply_ne (fun w => d.x w h) (ne_of_lt hab)
  have bounds (y : ℝ) (hy : y ∈ Set.uIcc h 1) : h ≤ y ∧ y ≤ 1 := by
    simpa only [Set.uIcc_of_le hh.le, Set.mem_Icc] using hy
  have covers (y : ℝ) (hy : y ∈ Set.uIcc h 1) : d.covers a y ∧ d.covers b y := by
    have hy' := bounds y hy
    exact ⟨⟨ha₀.1.le.trans hy'.1, ha₁.symm ▸ hy'.2⟩, hb₀.1.le.trans hy'.1,
      hb₁.symm ▸ hy'.2⟩
  refine Diagram.order_across covers (fun y hy => ?_) hab
  rcases eq_or_lt_of_le (bounds y hy).2 with hy' | hy'
  · rw [hy']
    exact d.output_boundary_separated hne fna fnb
  · have hhi : y < d.upper a := by rw [ha₁]; exact hy'
    exact d.separated hne ⟨ha₀.1.trans_le (bounds y hy).1, hhi⟩ (covers y hy).2

theorem input_order (s : d.Sweep) :
    (s.wires 0).Pairwise (fun a b => d.x a 0 < d.x b 0) :=
  input_boundary_order (s.ordered 0) (gap_inside d (s.cuts.in_gap 0)).1
    (fun w hw => (input_mem s w).mp hw)

theorem output_order (s : d.Sweep) :
    (s.wires (Fin.last V)).Pairwise (fun a b => d.x a 1 < d.x b 1) :=
  output_boundary_order (s.ordered _) (gap_inside d (s.cuts.in_gap _)).2
    (fun w hw => (output_mem s w).mp hw)

end Silmaril.RuntimeWires.Proofs.ProgressiveSweep
