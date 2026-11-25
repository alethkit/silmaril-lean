module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSimultaneous.Window
import Mathlib.Data.Fintype.Sum

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable {d : Diagram S V W .point} {height lo hi : ℝ}

private theorem positions_distinct {a b : Diagram.LayerSlot V W}
    (ha : d.atLayer height a) (hb : d.atLayer height b) (hne : a ≠ b) :
    d.slotX height a ≠ d.slotX height b := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have different : a ≠ b := fun eq => hne (congrArg Sum.inl eq)
      exact d.separated different ha ⟨hb.1.le, hb.2.le⟩
    | inr j =>
      change d.vertexHeight j = height at hb
      change d.x a height ≠ d.vertexX j
      exact hb ▸ d.avoids_vertex a j (hb.symm ▸ ha)
  | inr i =>
    cases b with
    | inl b =>
      change d.vertexHeight i = height at ha
      change d.vertexX i ≠ d.x b height
      exact (ha ▸ d.avoids_vertex b i (ha.symm ▸ hb)).symm
    | inr j =>
      intro eq
      have same_height : d.vertexHeight i = d.vertexHeight j := ha.trans hb.symm
      have same := d.vertex_separation (Prod.ext eq same_height)
      exact hne (congrArg Sum.inr same)

private theorem ordered_blocks {cut : ℝ} {slots : List (Diagram.LayerSlot V W)}
    (ports : Diagram.LayerSlot V W → List (Fin W))
    (order : slots.Pairwise (fun a b => d.slotX height a < d.slotX height b))
    (block : ∀ c ∈ slots, Block d height cut (ports c))
    (position : ∀ c ∈ slots, ∀ w ∈ ports c, d.x w height = d.slotX height c) :
    Block d height cut (slots.flatMap ports) := by
  induction slots with
  | nil => exact ⟨by simp, by simp, .nil⟩
  | cons head tail ih =>
    have first := block head List.mem_cons_self
    have rest := ih order.tail
      (fun c hc => block c (List.mem_cons_of_mem _ hc))
      (fun c hc => position c (List.mem_cons_of_mem _ hc))
    refine first.append rest (fun a ha b hb => ?_)
    obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hb
    rw [position head List.mem_cons_self a ha, position c (List.mem_cons_of_mem _ hc) b hb]
    exact (List.pairwise_cons.mp order).1 c hc

private theorem assemble_layer_cut {cut : ℝ} {slots : List (Diagram.LayerSlot V W)}
    {ports : Fin V → List (Fin W)}
    (exact_slots : ∀ c, c ∈ slots ↔ d.atLayer height c)
    (order : slots.Pairwise (fun a b => d.slotX height a < d.slotX height b))
    (classify : ∀ w, d.crosses w cut ↔
      d.crosses w height ∨ ∃ j, d.vertexHeight j = height ∧ w ∈ ports j)
    (port_block : ∀ j, d.vertexHeight j = height → Block d height cut (ports j))
    (port_position : ∀ j, d.vertexHeight j = height →
      ∀ w ∈ ports j, d.x w height = d.vertexX j) :
    d.OrderedCut cut (slots.flatMap (Sum.elim List.singleton ports)) := by
  have blocks := ordered_blocks (Sum.elim List.singleton ports) order (by
    intro c hc
    have h := (exact_slots c).mp hc
    cases c with
    | inl w =>
      change d.crosses w height at h
      have covers : d.covers w height := ⟨h.1.le, h.2.le⟩
      have crosses := (classify w).mpr (Or.inl h)
      exact ⟨fun z hz => List.mem_singleton.mp hz ▸ covers,
        fun z hz => List.mem_singleton.mp hz ▸ crosses, List.pairwise_singleton _ _⟩
    | inr j => exact port_block j h) (by
    intro c hc w hw
    cases c with
    | inl z => exact congrArg (fun a => d.x a height) (List.mem_singleton.mp hw)
    | inr j => exact port_position j ((exact_slots _).mp hc) w hw)
  refine ⟨?_, blocks.ordered⟩
  intro w
  rw [classify]
  constructor
  · intro hw
    obtain ⟨c, hc, hw⟩ := List.mem_flatMap.mp hw
    have h := (exact_slots c).mp hc
    cases c with
    | inl z =>
      have eq : w = z := List.mem_singleton.mp hw
      exact Or.inl (eq.symm ▸ h)
    | inr j => exact Or.inr ⟨j, h, hw⟩
  · rintro (hw | ⟨j, hj, hw⟩)
    · exact List.mem_flatMap.mpr ⟨.inl w, (exact_slots _).mpr hw, List.mem_singleton_self _⟩
    · exact List.mem_flatMap.mpr ⟨.inr j, (exact_slots _).mpr hj, hw⟩

theorem layer_slice (iso : d.IsolatesLayer height lo hi) : Nonempty (d.LayerSlice height lo hi) := by
  obtain ⟨slots, exact_slots, order⟩ :=
    sorted_coordinates (d.slotX height) (d.atLayer height) positions_distinct
  refine ⟨⟨iso, slots, exact_slots, order, ?_, ?_⟩⟩
  · refine assemble_layer_cut exact_slots order (layer_before_classify iso)
      (fun _ hj => layer_incoming iso hj) ?_
    intro j hj w hw
    rw [← hj]
    exact d.finish_attached w j ((input_mem j w).mp hw)
  · refine assemble_layer_cut exact_slots order (layer_after_classify iso)
      (fun _ hj => layer_outgoing iso hj) ?_
    intro j hj w hw
    rw [← hj]
    exact d.start_attached w j ((output_mem j w).mp hw)

variable (s : d.LayerSlice height lo hi)

theorem vertices_exact (j : Fin V) : j ∈ s.vertices ↔ d.vertexHeight j = height := by
  rw [Diagram.LayerSlice.vertices, List.mem_filterMap]
  constructor
  · rintro ⟨slot, hs, he⟩
    cases slot with
    | inl w => contradiction
    | inr i =>
      have eq : i = j := Option.some.inj he
      subst i
      exact (s.exact_slots _).mp hs
  · intro hh
    exact ⟨.inr j, (s.exact_slots _).mpr hh, rfl⟩

theorem vertices_order : s.vertices.Pairwise (fun i j => d.vertexX i < d.vertexX j) := by
  apply s.ordered.filterMap Sum.getRight?
  rintro (w | i) (z | j) order a ha b hb
  all_goals simp [Sum.getRight?] at ha hb
  cases ha
  cases hb
  exact order

theorem layer_input_types :
    (s.slots.flatMap d.slotInputs).map d.label = s.slots.flatMap d.slotSource := by
  rw [List.map_flatMap]
  congr 1
  funext slot
  cases slot with
  | inl w => rfl
  | inr j => simp [Diagram.slotInputs, Diagram.slotSource, Diagram.inputs, d.input_types]

theorem layer_output_types :
    (s.slots.flatMap d.slotOutputs).map d.label = s.slots.flatMap d.slotTarget := by
  rw [List.map_flatMap]
  congr 1
  funext slot
  cases slot with
  | inl w => rfl
  | inr j => simp [Diagram.slotOutputs, Diagram.slotTarget, Diagram.outputs, d.output_types]

end Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous
