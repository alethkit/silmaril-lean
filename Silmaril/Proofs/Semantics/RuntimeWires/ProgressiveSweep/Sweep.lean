module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSweep.Heights
public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSweep

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} (d : Diagram S V W)

noncomputable def sweep : d.Sweep where
  wires i := Classical.choose (d.ordered_cut_exists (d.cutHeight i))
  ordered i := Classical.choose_spec (d.ordered_cut_exists (d.cutHeight i))
  event i := Classical.choice (Diagram.single_event (cut_isolates d i))
  before i := Diagram.ordered_cut_unique
    (Classical.choice (Diagram.single_event (cut_isolates d i))).before
    (Classical.choose_spec (d.ordered_cut_exists (d.cutHeight i.castSucc)))
  after i := Diagram.ordered_cut_unique
    (Classical.choice (Diagram.single_event (cut_isolates d i))).after
    (Classical.choose_spec (d.ordered_cut_exists (d.cutHeight i.succ)))

variable {d}

theorem wire_span (s : d.Sweep) (i : Fin (V + 1)) (w : Fin W) :
    w ∈ s.wires i ↔ (d.startIndex w).val ≤ i.val ∧ i.val < (d.finishIndex w).val :=
  ((s.ordered i).exact_wires w).trans (crosses_iff_indices d i w)

theorem some_cut (s : d.Sweep) (w : Fin W) : ∃ i, w ∈ s.wires i := by
  have he := endpoint_indices d w
  have hb : (d.startIndex w).val < V + 1 := by
    have h := (d.finishIndex w).isLt
    change (d.startIndex w).val < (d.finishIndex w).val at he
    omega
  exact ⟨⟨_, hb⟩, (wire_span s _ w).mpr ⟨le_rfl, he⟩⟩

theorem wire_input (i : Fin V) (w : Fin W) :
    w ∈ d.inputs (d.vertexOrder i) ↔ (d.finishIndex w).val = i.val + 1 := by
  rw [Diagram.inputs, List.mem_ofFn, ← d.input_exact]
  cases hf : d.finish w with
  | none =>
    have h := i.isLt
    constructor
    · intro he
      contradiction
    · intro he
      have eq : V + 1 = i.val + 1 := by simpa [Diagram.finishIndex, hf] using he
      omega
  | some v =>
    simp only [Diagram.finishIndex, hf, Option.elim_some, Diagram.vertexIndex, Fin.val_succ,
      Fin.val_castSucc, Option.some.injEq, Nat.add_right_cancel_iff]
    exact ⟨fun h => congrArg Fin.val (h ▸ (d.vertexOrder.symm_apply_apply i)),
      fun h => (d.vertexOrder.apply_symm_apply v).symm.trans (congrArg d.vertexOrder (Fin.ext h))⟩

theorem wire_output (i : Fin V) (w : Fin W) :
    w ∈ d.outputs (d.vertexOrder i) ↔ (d.startIndex w).val = i.val + 1 := by
  rw [Diagram.outputs, List.mem_ofFn, ← d.output_exact]
  cases hs : d.start w with
  | none => simp [Diagram.startIndex, hs]
  | some v =>
    simp only [Diagram.startIndex, hs, Option.elim_some, Diagram.vertexIndex, Fin.val_succ,
      Fin.val_castSucc, Option.some.injEq, Nat.add_right_cancel_iff]
    exact ⟨fun h => congrArg Fin.val (h ▸ (d.vertexOrder.symm_apply_apply i)),
      fun h => (d.vertexOrder.apply_symm_apply v).symm.trans (congrArg d.vertexOrder (Fin.ext h))⟩

end Silmaril.RuntimeWires.Proofs.ProgressiveSweep
