module

public import Silmaril.Semantics.RuntimeWires.SerialTrace.Defs
import Silmaril.Semantics.RuntimeWires.ProgressiveTrace.Thms

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.SerialTrace

open Silmaril.RuntimeWires.ProgressiveGraph Silmaril.RuntimeWires.Sliced

universe u v

def rowsBefore {n : ℕ} {α : Type*} (orders : Fin n → List α) (i : ℕ) : ℕ :=
  ((List.ofFn orders).take i).flatten.length

theorem rowsBefore_zero {n : ℕ} {α : Type*} (orders : Fin n → List α) :
    rowsBefore orders 0 = 0 := by simp [rowsBefore]

theorem rowsBefore_succ {n : ℕ} {α : Type*} (orders : Fin (n + 1) → List α) (i : ℕ) :
    rowsBefore orders (i + 1) = (orders 0).length + rowsBefore (orders ∘ Fin.succ) i := by
  simp [rowsBefore, List.ofFn_succ, Function.comp_def]

private theorem idxOf_layers {n : ℕ} {α : Type*} [BEq α] [LawfulBEq α]
    (orders : Fin n → List α) (i : Fin n) (v : α)
    (atLevel : v ∈ orders i) (elsewhere : ∀ j, j ≠ i → v ∉ orders j) :
    ((List.ofFn orders).flatten).idxOf v = rowsBefore orders i.val + (orders i).idxOf v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert atLevel elsewhere
    refine Fin.cases ?_ (fun j => ?_) i
    · intro head _
      simp [List.ofFn_succ, List.idxOf_append, head, rowsBefore_zero]
    · intro atTail other
      have notHead := other 0 (Fin.ne_of_lt (Fin.succ_pos j))
      have left := ih (orders ∘ Fin.succ) j atTail
        (fun k hk => other k.succ (fun h => hk (Fin.succ_injective _ h)))
      simp only [List.ofFn_succ, List.flatten_cons, List.idxOf_append, notHead, ite_false,
        Fin.val_succ, rowsBefore_succ]
      change ((List.ofFn (orders ∘ Fin.succ)).flatten).idxOf v + (orders 0).length = _
      rw [left]
      simp only [Function.comp_apply]
      omega

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W .point}
variable {s : d.LayerSweep} (p : s.Schedule)

theorem mem_order (i : Fin d.levelCount) (v : Fin V) :
    v ∈ p.order i ↔ d.levelIndex v = i :=
  (p.perm i).mem_iff.trans (s.vertex_mem i v)

theorem order_nodup (i : Fin d.levelCount) : (p.order i).Nodup :=
  (p.perm i).nodup_iff.mpr
    ((s.layer i).vertices_order.imp (fun h => ne_of_apply_ne d.vertexX (ne_of_lt h)))

theorem mem_slot {i : Fin d.levelCount} {v : Fin V} (h : v ∈ p.order i) :
    Sum.inr v ∈ (s.layer i).slots :=
  ((s.layer i).exact_slots _).mpr (((s.layer i).vertices_exact v).mp ((p.perm i).mem_iff.mp h))

theorem row_index (i : Fin d.levelCount) (v : Fin V) (hv : v ∈ p.order i) :
    p.serialRow v = rowsBefore p.order i.val + (p.order i).idxOf v :=
  idxOf_layers p.order i v hv (fun j h hj => h (((mem_order p j v).mp hj).symm.trans ((mem_order p i v).mp hv)))

theorem origin_injective : Function.Injective p.origin := by
  intro w z eq
  rcases hw : d.start w with _ | a <;> rcases hz : d.start z with _ | b
  · have hi : (s.wires 0).idxOf w = (s.wires 0).idxOf z :=
      WireOrigin.boundary.inj (by simpa [Diagram.LayerSweep.Schedule.origin, hw, hz] using eq)
    exact (List.idxOf_inj ((s.input_mem w).mpr hw)).mp hi
  · simp [Diagram.LayerSweep.Schedule.origin, hw, hz] at eq
  · simp [Diagram.LayerSweep.Schedule.origin, hw, hz] at eq
  · have he : WireOrigin.box (p.serialRow a) 0 ((d.outputs a).idxOf w) =
        WireOrigin.box (p.serialRow b) 0 ((d.outputs b).idxOf z) := by
      simpa [Diagram.LayerSweep.Schedule.origin, hw, hz] using eq
    obtain ⟨rows, _, ports⟩ := WireOrigin.box.inj he
    have mem : a ∈ p.vertices :=
      List.mem_flatten.mpr ⟨p.order (d.levelIndex a), List.mem_ofFn.mpr ⟨_, rfl⟩,
        (mem_order p _ a).mpr rfl⟩
    have same : a = b := (List.idxOf_inj mem).mp rows
    subst b
    exact (List.idxOf_inj (List.mem_ofFn.mpr ((d.output_exact a w).mp hw))).mp ports

theorem rename_origin (w : Fin W) : p.renameOrigin (s.origin w) = some (p.origin w) := by
  cases start : d.start w with
  | none => simp [Diagram.LayerSweep.origin, Diagram.LayerSweep.Schedule.origin,
      Diagram.LayerSweep.Schedule.renameOrigin, start]
  | some v =>
    let vertices := (s.layer (d.levelIndex v)).vertices
    have mem : v ∈ vertices := (s.vertex_mem _ v).mpr rfl
    have hb := List.idxOf_lt_length_iff.mpr mem
    have lookup : vertices[vertices.idxOf v]? = some v := by
      rw [List.getElem?_eq_getElem hb, List.getElem_idxOf]
    simp only [Diagram.LayerSweep.origin, Diagram.LayerSweep.Schedule.origin, start,
      Diagram.LayerSweep.Schedule.renameOrigin, dite_eq_left (d.levelIndex v).isLt,
      Diagram.LayerSweep.boxOrdinal]
    exact congrArg (Option.map (fun x => WireOrigin.box (p.serialRow x) 0 ((d.outputs v).idxOf w))) lookup

theorem boundary_names :
    namePorts .boundary (s.word 0) = (s.wires 0).map p.namedWire := by
  rw [Diagram.LayerSweep.word, namePorts_map _ (s.ordered 0).nodup]
  apply List.map_congr_left
  intro w hw
  simp [Diagram.LayerSweep.Schedule.namedWire, Diagram.LayerSweep.Schedule.origin,
    (s.input_mem w).mp hw]

theorem output_names (i : Fin d.levelCount) (v : Fin V) (hv : v ∈ p.order i) :
    namePorts (.box (rowsBefore p.order i.val + (p.order i).idxOf v) 0) (S.target (d.generator v)) =
      (d.outputs v).map p.namedWire := by
  have nd : (d.outputs v).Nodup :=
    (List.nodup_flatMap.mp (s.layer i).after.nodup).1 _ (mem_slot p hv)
  rw [← d.output_types v]
  change namePorts _ ((d.outputs v).map d.label) = _
  rw [namePorts_map _ nd]
  apply List.map_congr_left
  intro w hw
  have start : d.start w = some v := (d.output_exact v w).mpr (List.mem_ofFn.mp hw)
  simp [Diagram.LayerSweep.Schedule.namedWire, Diagram.LayerSweep.Schedule.origin, start,
    row_index p i v hv]

end Silmaril.RuntimeWires.Proofs.SerialTrace
