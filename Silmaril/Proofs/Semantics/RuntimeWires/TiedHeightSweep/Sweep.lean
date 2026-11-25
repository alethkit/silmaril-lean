module

public import Silmaril.Proofs.Semantics.RuntimeWires.TiedHeightSweep.Heights
import Silmaril.Semantics.RuntimeWires.ProgressiveCutChoice.Thms
import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.TiedHeightSweep

open Silmaril.RuntimeWires.ProgressiveGraph
open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable {d : ProgressiveGraph.Diagram S V W .point}

noncomputable def sweepAt (d : ProgressiveGraph.Diagram S V W .point) (cuts : d.LayerCuts) :
    d.LayerSweep :=
  let ordered i := d.ordered_cut_exists (cuts.height i)
  let layer i := Classical.choice (Diagram.layer_slice (gap_isolates d i (cuts.in_gap _) (cuts.in_gap _)))
  ⟨cuts, fun i => Classical.choose (ordered i), fun i => Classical.choose_spec (ordered i), layer,
    fun i => Diagram.ordered_cut_unique (layer i).before (Classical.choose_spec (ordered _)),
    fun i => Diagram.ordered_cut_unique (layer i).after (Classical.choose_spec (ordered _))⟩

theorem sweepAt_cuts (d : ProgressiveGraph.Diagram S V W .point) (cuts : d.LayerCuts) :
    (sweepAt d cuts).cuts = cuts := by
  unfold sweepAt
  rfl

variable (s : d.LayerSweep)

theorem wire_span (i : Fin (d.levelCount + 1)) (w : Fin W) :
    w ∈ s.wires i ↔ (d.layerStartIndex w).val ≤ i.val ∧ i.val < (d.layerFinishIndex w).val :=
  ((s.ordered i).exact_wires w).trans (gap_crosses_iff_indices d (s.cuts.in_gap i) w)

theorem some_cut (w : Fin W) : ∃ i, w ∈ s.wires i := by
  have he := endpoint_ranks d w
  have hb : (d.layerStartIndex w).val < d.levelCount + 1 := by
    have h := (d.layerFinishIndex w).isLt
    change (d.layerStartIndex w).val < (d.layerFinishIndex w).val at he
    omega
  exact ⟨⟨_, hb⟩, (wire_span s _ w).mpr ⟨le_rfl, he⟩⟩

theorem input_mem (w : Fin W) : w ∈ s.wires 0 ↔ d.start w = none := by
  rw [wire_span]
  have hf : 0 < (d.layerFinishIndex w).val := (Nat.zero_le _).trans_lt (endpoint_ranks d w)
  cases hw : d.start w <;> simp [Diagram.layerStartIndex, hw, hf]

theorem output_mem (w : Fin W) : w ∈ s.wires (Fin.last d.levelCount) ↔ d.finish w = none := by
  rw [wire_span]
  change (d.layerStartIndex w).val ≤ d.levelCount ∧ d.levelCount < (d.layerFinishIndex w).val ↔ _
  cases hw : d.finish w with
  | none =>
    have h : (d.layerStartIndex w).val < d.levelCount + 1 := by
      have he := endpoint_ranks d w
      change (d.layerStartIndex w).val < (d.layerFinishIndex w).val at he
      simpa only [Diagram.layerFinishIndex, hw, Option.elim_none, Fin.val_last] using he
    simp [Diagram.layerFinishIndex, hw, Nat.lt_succ_iff.mp h]
  | some v =>
    have hv := (d.levelIndex v).isLt
    have hf : ¬ d.levelCount < (d.layerFinishIndex w).val := by
      simp only [Diagram.layerFinishIndex, hw, Option.elim_some, Fin.val_succ, Fin.val_castSucc]
      omega
    simp [hf]

theorem input_order : (s.wires 0).Pairwise (fun a b => d.x a 0 < d.x b 0) :=
  (s.ordered 0).input_boundary_order (gap_inside d (s.cuts.in_gap 0)).1
    (fun w hw => (input_mem s w).mp hw)

theorem output_order : (s.wires (Fin.last d.levelCount)).Pairwise (fun a b => d.x a 1 < d.x b 1) :=
  (s.ordered _).output_boundary_order (gap_inside d (s.cuts.in_gap _)).2
    (fun w hw => (output_mem s w).mp hw)

theorem wires_eq (t : d.LayerSweep) (i : Fin (d.levelCount + 1)) : s.wires i = t.wires i := by
  have hh := s.cuts.in_gap i
  have hk := t.cuts.in_gap i
  refine Diagram.ordered_cut_unique ((s.ordered i).relocate_active (fun w y hy => ?_)) (t.ordered i)
  have hg : y ∈ d.levelGap i :=
    ⟨(lt_min hh.1 hk.1).trans_le hy.1, hy.2.trans_lt (max_lt hh.2 hk.2)⟩
  exact (gap_crosses_iff_indices d hh w).trans (gap_crosses_iff_indices d hg w).symm

private theorem slots_eq (t : d.LayerSweep) (i : Fin d.levelCount) :
    (s.layer i).slots = (t.layer i).slots := by
  let atHeight := d.slotX (d.levelHeight i)
  have nodup (u : d.LayerSweep) : (u.layer i).slots.Nodup :=
    (u.layer i).ordered.imp (fun h => ne_of_apply_ne atHeight (ne_of_lt h))
  have perm := (List.perm_ext_iff_of_nodup (nodup s) (nodup t)).mpr
    (fun c => ((s.layer i).exact_slots c).trans ((t.layer i).exact_slots c).symm)
  exact perm.eq_of_pairwise (fun _ _ _ _ h k => (lt_asymm h k).elim)
    (s.layer i).ordered (t.layer i).ordered

private theorem reindex_heq {A B X Y : List O} (a : A = X) (b : B = Y) (r : Row S A B) :
    HEq (r.reindex a b) r := by
  subst a
  subst b
  rfl

private theorem row_to_layer (i : Fin d.levelCount) : HEq (s.row i) (s.layer i).row :=
  (reindex_heq _ _ (s.layer i).cutRow).trans (reindex_heq _ _ (s.layer i).row)

private theorem layerRow_heq {a b : List (Diagram.LayerSlot V W)} (h : a = b) :
    HEq (d.layerRow a) (d.layerRow b) := by
  subst b
  rfl

theorem sheet_eq (t : d.LayerSweep) :
    (congrArg₂ (Sheet S) (congrArg (List.map d.label) (wires_eq s t 0))
      (congrArg (List.map d.label) (wires_eq s t (Fin.last d.levelCount)))).mp s.sheet = t.sheet := by
  have words : s.word = t.word := funext (fun i => congrArg (List.map d.label) (wires_eq s t i))
  exact Diagram.Sweep.joinRows_eq words s.row t.row (fun i =>
    (row_to_layer s i).trans ((layerRow_heq (slots_eq s t i)).trans (row_to_layer t i).symm))

private theorem join_serial_seam {n : ℕ} (word : Fin (n + 1) → List O)
    (row : ∀ i : Fin n, Row S (word i.castSucc) (word i.succ))
    (segment : ∀ i : Fin n, Sheet S (word i.castSucc) (word i.succ))
    (equiv : ∀ i, Sheet.SeamEquivalent (segment i) (.cons (row i) (.empty _))) :
    Sheet.SeamEquivalent (Sheet.joinSegments word segment) (Diagram.Sweep.joinRows word row) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    exact (equiv 0).thenDo (ih (word ∘ Fin.succ) (fun i => row i.succ)
      (fun i => segment i.succ) (fun i => equiv i.succ))

theorem serial_seam (p : s.Schedule) : Sheet.SeamEquivalent (s.serialSheet p) s.sheet := by
  apply join_serial_seam s.word s.row (s.serialSegment p)
  intro i
  have h := ((s.layer i).serializeCuts_seam (p.order i) (p.perm i)).reindex
    (congrArg (List.map d.label) (s.before i)) (congrArg (List.map d.label) (s.after i))
  simpa only [Diagram.LayerSweep.serialSegment, Diagram.LayerSweep.row, Diagram.LayerSweep.word,
    Sheet.reindex_single] using h

end Silmaril.RuntimeWires.Proofs.TiedHeightSweep
