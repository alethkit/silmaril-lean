module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Defs
public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Thms
import Mathlib.Data.List.OfFn

public section

namespace Silmaril.RuntimeWires.Proofs.CapReadout

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : CapProfile O}

/-- Recover the specified cap enumeration from its coverage and order. -/
private theorem cap_word {W : ℕ} {cap : CapProfile O} {atCap : Fin W → Prop}
    (slots : Fin cap.size ≃ {w : Fin W // atCap w})
    (x : Fin W → ℝ) (label : Fin W → O) (wires : List (Fin W))
    (mem : ∀ w, w ∈ wires ↔ atCap w)
    (ordered : wires.Pairwise fun i j => x i < x j)
    (atSlot : ∀ i, x (slots i).val = cap.x i)
    (typed : ∀ i, label (slots i).val = cap.label i) :
    wires.map label = List.ofFn cap.label := by
  let listed := List.ofFn fun i => (slots i).val
  have listed_ordered : listed.Pairwise (fun i j => x i < x j) :=
    List.pairwise_ofFn.mpr fun i j lt => by
      rw [atSlot i, atSlot j]
      exact cap.ordered lt
  have nodup (xs : List (Fin W)) (h : xs.Pairwise (fun i j => x i < x j)) : xs.Nodup :=
    h.imp fun lt => ne_of_apply_ne x (ne_of_lt lt)
  have same (w : Fin W) : w ∈ wires ↔ w ∈ listed := by
    rw [mem, List.mem_ofFn]
    exact ⟨fun hw => ⟨slots.symm ⟨w, hw⟩, congrArg Subtype.val (slots.apply_symm_apply _)⟩,
      fun ⟨i, eq⟩ => eq ▸ (slots i).property⟩
  have perm := (List.perm_ext_iff_of_nodup (nodup _ ordered) (nodup _ listed_ordered)).mpr same
  have ids := perm.eq_of_pairwise (fun _ _ _ _ h k => (lt_asymm h k).elim) ordered listed_ordered
  rw [ids, List.map_ofFn]
  exact congrArg List.ofFn (funext typed)

theorem input_word (p : FixedDrawing S a b) (s : p.drawing.LayerSweep) :
    s.word 0 = List.ofFn a.label :=
  cap_word p.input (fun w => p.drawing.x w 0) p.drawing.label (s.wires 0)
    s.input_mem s.input_order p.input_x p.input_label

theorem output_word (p : FixedDrawing S a b) (s : p.drawing.LayerSweep) :
    s.word (Fin.last p.drawing.levelCount) = List.ofFn b.label :=
  cap_word p.output (fun w => p.drawing.x w 1) p.drawing.label
    (s.wires (Fin.last p.drawing.levelCount))
    s.output_mem s.output_order p.output_x p.output_label

end Silmaril.RuntimeWires.Proofs.CapReadout
