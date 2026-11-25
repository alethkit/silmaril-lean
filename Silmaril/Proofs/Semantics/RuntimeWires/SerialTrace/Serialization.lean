module

public import Silmaril.Proofs.Semantics.RuntimeWires.SerialTrace.Step

public section

namespace Silmaril.RuntimeWires.Proofs.SerialTrace

open Silmaril.RuntimeWires.ProgressiveGraph Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable (d : ProgressiveGraph.Diagram S V W .point)
variable (name : Fin W → NamedWire O)

theorem trace_serializeFrom (slots : List (Diagram.LayerSlot V W)) (slotNd : slots.Nodup)
    (done : Finset (Fin V)) (order : List (Fin V)) (orderNd : order.Nodup) (offset : ℕ)
    (present : ∀ j ∈ order, Sum.inr j ∈ slots) (fresh : ∀ j ∈ order, j ∉ done)
    (outputs : ∀ j ∈ order,
      namePorts (.box (offset + order.idxOf j) 0) (S.target (d.generator j)) = (d.outputs j).map name) :
    (d.serializeFrom slots done order).traceWiresFrom offset ((d.frontierWires done slots).map name) =
      ⟨order.map (fun j => [boxTrace d name j]),
        (d.frontierWires (Diagram.completed done order) slots).map name⟩ := by
  induction order generalizing offset done with
  | nil => rfl
  | cons j order ih =>
    have once := List.nodup_cons.mp orderNd
    have head := trace_step d name slots done j (fresh j List.mem_cons_self) slotNd offset 0 (fun _ => by
      simpa using outputs j List.mem_cons_self)
    have headSlot := present j List.mem_cons_self
    have tail := ih (insert j done) once.2 (offset + 1)
      (fun k hk => present k (.tail _ hk))
      (fun k hk => by
        have different : k ≠ j := fun eq => once.1 (eq ▸ hk)
        simp [Finset.mem_insert, different, fresh k (.tail _ hk)])
      (fun k hk => by
        have different : j ≠ k := fun eq => once.1 (eq.symm ▸ hk)
        have names := outputs k (.tail _ hk)
        have shift : offset + (order.idxOf k).succ = offset + 1 + order.idxOf k := by omega
        rwa [List.idxOf_cons_ne _ different, shift] at names)
    simp only [Diagram.serializeFrom, Sheet.traceWiresFrom, head, ite_eq_left headSlot, List.map_cons]
    exact congrArg (fun rest => SheetTrace.mk ([boxTrace d name j] :: rest.rows) rest.outputs) tail

theorem frontierWires_empty (slots : List (Diagram.LayerSlot V W)) :
    d.frontierWires ∅ slots = slots.flatMap d.slotInputs := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    cases slot
    · change _ :: d.frontierWires ∅ slots = _ :: slots.flatMap d.slotInputs
      rw [ih]
    · change d.inputs _ ++ d.frontierWires ∅ slots = d.inputs _ ++ slots.flatMap d.slotInputs
      rw [ih]

theorem frontierWires_full (slots : List (Diagram.LayerSlot V W)) (done : Finset (Fin V))
    (covers : ∀ j, Sum.inr j ∈ slots → j ∈ done) :
    d.frontierWires done slots = slots.flatMap d.slotOutputs := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    have tail := ih (fun j hj => covers j (.tail _ hj))
    cases slot with
    | inl w =>
      change w :: d.frontierWires done slots = w :: slots.flatMap d.slotOutputs
      rw [tail]
    | inr v =>
      have head := covers v List.mem_cons_self
      change d.vertexWires v (decide (v ∈ done)) ++ d.frontierWires done slots =
        d.outputs v ++ slots.flatMap d.slotOutputs
      simp [head, Diagram.vertexWires, tail]

theorem trace_reindex {A B C D : List O} (hA : A = C) (hB : B = D) (p : Sheet S A B)
    (row : ℕ) (input : List (NamedWire O)) :
    (p.reindex hA hB).traceWiresFrom row input = p.traceWiresFrom row input := by
  subst C
  subst D
  rfl

end Silmaril.RuntimeWires.Proofs.SerialTrace
