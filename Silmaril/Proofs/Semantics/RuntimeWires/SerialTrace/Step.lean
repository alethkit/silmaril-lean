module

public import Silmaril.Semantics.RuntimeWires.SerialTrace.Defs
import Silmaril.Semantics.RuntimeWires.ProgressiveTrace.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.SerialTrace

open Silmaril.RuntimeWires.ProgressiveGraph Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable (d : ProgressiveGraph.Diagram S V W .point)
variable (name : Fin W → NamedWire O)

@[expose] def boxTrace (j : Fin V) : BoxTrace S :=
  ⟨d.generator j, (d.inputs j).map name, (d.outputs j).map name⟩

private theorem port_count (j : Fin V) (done : Bool) :
    ((d.vertexWires j done).map name).length = (d.vertexWord j done).length := by
  cases done <;> simp [Diagram.vertexWires, Diagram.vertexWord, Diagram.inputs, Diagram.outputs]

private theorem trace_pass_vertex (j : Fin V) (a b : Bool) (same : a = b)
    (mono : a = true → b = true) {A B : List O} (tail : Row S A B)
    (row box : ℕ) (input : List (NamedWire O)) :
    (d.vertexStep j a b mono tail).traceWires row box ((d.vertexWires j a).map name ++ input) =
      ⟨(d.vertexWires j b).map name ++ (tail.traceWires row box input).frontier,
        (tail.traceWires row box input).boxes⟩ := by
  subst b
  cases a
  · exact Row.traceWires_pass tail _ _ input (port_count d name j false) row box
  · exact Row.traceWires_pass tail _ _ input (port_count d name j true) row box

private theorem trace_fire_vertex (j : Fin V) (a b : Bool) (pending : a = false) (done : b = true)
    (mono : a = true → b = true) {A B : List O} (tail : Row S A B)
    (row box : ℕ) (input : List (NamedWire O))
    (outputs : namePorts (.box row box) (S.target (d.generator j)) = (d.outputs j).map name) :
    (d.vertexStep j a b mono tail).traceWires row box ((d.vertexWires j a).map name ++ input) =
      ⟨(d.vertexWires j b).map name ++ (tail.traceWires row (box + 1) input).frontier,
        boxTrace d name j :: (tail.traceWires row (box + 1) input).boxes⟩ := by
  subst a
  subst b
  have count := port_count d name j false
  simp only [Diagram.vertexStep, Diagram.vertexWires, Diagram.vertexWord] at count ⊢
  simp only [Row.traceWires, List.take_left' count, List.drop_left' count, outputs, boxTrace]

theorem trace_step (slots : List (Diagram.LayerSlot V W)) (done : Finset (Fin V))
    (j : Fin V) (fresh : j ∉ done) (nd : slots.Nodup) (row box : ℕ)
    (outputs : Sum.inr j ∈ slots →
      namePorts (.box row box) (S.target (d.generator j)) = (d.outputs j).map name) :
    (d.layerStep (Finset.subset_insert j done) slots).traceWires row box
        ((d.frontierWires done slots).map name) =
      ⟨(d.frontierWires (insert j done) slots).map name,
        if Sum.inr j ∈ slots then [boxTrace d name j] else []⟩ := by
  induction slots generalizing box with
  | nil => rfl
  | cons slot slots ih =>
    have tailNd := (List.nodup_cons.mp nd).2
    cases slot with
    | inl w =>
      have tail := ih tailNd box (fun h => outputs (.tail _ h))
      change (.wire (d.label w) (d.layerStep (Finset.subset_insert j done) slots) : Row S _ _).traceWires
        row box (name w :: (d.frontierWires done slots).map name) =
        ⟨name w :: (d.frontierWires (insert j done) slots).map name, _⟩
      simp [Row.traceWires, tail]
    | inr v =>
      simp only [Diagram.layerStep, Diagram.frontierWires, List.map_append]
      by_cases same : v = j
      · subst v
        have absent : Sum.inr j ∉ slots := (List.nodup_cons.mp nd).1
        have tail := ih tailNd (box + 1) (fun h => (absent h).elim)
        have fire := trace_fire_vertex d name j (decide (j ∈ done)) (decide (j ∈ insert j done))
          (by simp [fresh]) (by simp) (fun _ => by simp) (d.layerStep (Finset.subset_insert j done) slots)
          row box ((d.frontierWires done slots).map name) (outputs List.mem_cons_self)
        refine fire.trans ?_
        rw [tail]
        simp [absent]
      · have tail := ih tailNd box (fun h => outputs (.tail _ h))
        have membership : decide (v ∈ done) = decide (v ∈ insert j done) := by
          simp [Finset.mem_insert, same]
        have pass := trace_pass_vertex d name v _ _ membership (fun h => membership ▸ h)
          (d.layerStep (Finset.subset_insert j done) slots) row box ((d.frontierWires done slots).map name)
        refine pass.trans ?_
        rw [tail]
        simp [same, Ne.symm same]

end Silmaril.RuntimeWires.Proofs.SerialTrace
