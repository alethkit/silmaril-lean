module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialSweepRows
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepFrontiers
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.ProgressiveGluing

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)
variable (p : lower.LayerSweep) (q : upper.LayerSweep) (s : m.glue.LayerSweep)

theorem wires_lower (i : Fin (lower.levelCount + 1)) :
    s.wires ((sweepStack m).lowerCut i) = (p.wires i).map lowerId :=
  read_at s _ ((sweepStack m).lower_gap (p.cuts.in_gap i))
    (m.cut_lower (lower.level_gap_regular (p.cuts.in_gap i)).1.2 (p.ordered i))

theorem wires_upper (i : Fin (upper.levelCount + 1)) :
    s.wires ((sweepStack m).upperCut i) = (q.wires i).map m.upperId :=
  read_at s _ ((sweepStack m).upper_gap (q.cuts.in_gap i))
    (m.cut_upper (upper.level_gap_regular (q.cuts.in_gap i)).1.1 (q.ordered i))

theorem ordered_join_lower :
    m.glue.OrderedCut (1 / 2) ((p.wires (Fin.last lower.levelCount)).map lowerId) := by
  constructor
  · intro z
    rw [List.mem_map, m.crosses_join_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      let c : Contact lower := ⟨w, (p.output_mem w).mp hw⟩
      exact ⟨c, (m.lowerId_shared c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c.val, (p.output_mem c.val).mpr c.property, m.lowerId_shared c⟩
  · apply List.pairwise_map.mpr
    apply p.output_order.imp
    intro a b lt
    rw [m.glue_x_lower a le_rfl, m.glue_x_lower b le_rfl]
    simpa only [show slabHeight 0 (1 / 2) = 1 by norm_num [slabHeight]] using lt

theorem ordered_join_upper :
    m.glue.OrderedCut (1 / 2) ((q.wires 0).map m.upperId) := by
  constructor
  · intro z
    rw [List.mem_map, m.crosses_join_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      let c := m.contact.symm ⟨w, (q.input_mem w).mp hw⟩
      have eq : (m.contact c).val = w := congrArg Subtype.val (m.contact.apply_symm_apply _)
      exact ⟨c, ((congrArg m.upperId eq).symm.trans (m.upperId_shared c)).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨(m.contact c).val, (q.input_mem _).mpr (m.contact c).property, m.upperId_shared c⟩
  · apply List.pairwise_map.mpr
    apply q.input_order.imp
    intro a b lt
    rw [m.glue_x_upper a le_rfl, m.glue_x_upper b le_rfl]
    simpa only [show slabHeight 1 (1 / 2) = 0 by norm_num [slabHeight]] using lt

theorem wires_join_lower :
    s.wires (sweepStack m).joinCut = (p.wires (Fin.last lower.levelCount)).map lowerId :=
  read_at s _ (sweepStack m).join_gap (ordered_join_lower m p)

theorem wires_join_upper :
    s.wires (sweepStack m).joinCut = (q.wires 0).map m.upperId :=
  read_at s _ (sweepStack m).join_gap (ordered_join_upper m q)

theorem ordered_at_join : m.glue.OrderedCut (1 / 2) (s.wires (sweepStack m).joinCut) :=
  (wires_join_lower m lower.layerSweep s).symm ▸ ordered_join_lower m lower.layerSweep

theorem wires_first : s.wires 0 = (p.wires 0).map lowerId := by
  have eq : (sweepStack m).lowerCut 0 = 0 := rfl
  rw [← eq]
  exact wires_lower m p s 0

theorem wires_last : s.wires (Fin.last m.glue.levelCount) = (q.wires (Fin.last upper.levelCount)).map m.upperId := by
  have eq : (sweepStack m).upperCut (Fin.last upper.levelCount) = Fin.last m.glue.levelCount :=
    Fin.ext (sweepStack m).count_glue.symm
  rw [← eq]
  exact wires_upper m q s _

theorem first_word : s.word 0 = p.word 0 := by
  simp only [LayerSweep.word, wires_first m p s, List.map_map]
  exact congrArg (fun label => (p.wires 0).map label) (funext m.glue_label_lower)

theorem last_word : s.word (Fin.last m.glue.levelCount) = q.word (Fin.last upper.levelCount) := by
  simp only [LayerSweep.word, wires_last m q s, List.map_map]
  exact congrArg (fun label => (q.wires _).map label) (funext m.glue_label_upper)

theorem lower_join_word : s.word (sweepStack m).joinCut = p.word (Fin.last lower.levelCount) := by
  simp only [LayerSweep.word, wires_join_lower m p s, List.map_map]
  exact congrArg (fun label => (p.wires _).map label) (funext m.glue_label_lower)

theorem upper_join_word : s.word (sweepStack m).joinCut = q.word 0 := by
  simp only [LayerSweep.word, wires_join_upper m q s, List.map_map]
  exact congrArg (fun label => (q.wires 0).map label) (funext m.glue_label_upper)

include m in
theorem join_word : q.word 0 = p.word (Fin.last lower.levelCount) :=
  (upper_join_word m q m.glue.layerSweep).symm.trans (lower_join_word m p m.glue.layerSweep)

private theorem lower_only_absent (w : Fin A) (notAtCap : lower.finish w ≠ none)
    (i : Fin (upper.levelCount + 1)) : lowerId w ∉ s.wires ((sweepStack m).upperCut i) := by
  rw [wires_upper m upper.layerSweep s, List.mem_map]
  rintro ⟨other, _, eq⟩
  obtain ⟨contact, hw, _⟩ := m.lowerId_eq_upperId.mp eq.symm
  exact notAtCap (hw ▸ contact.property)

private theorem upper_only_absent (w : Fin B) (notAtCap : upper.start w ≠ none)
    (i : Fin (lower.levelCount + 1)) : m.upperId w ∉ s.wires ((sweepStack m).lowerCut i) := by
  rw [wires_lower m lower.layerSweep s, List.mem_map]
  rintro ⟨other, _, eq⟩
  obtain ⟨contact, _, hw⟩ := m.lowerId_eq_upperId.mp eq
  exact notAtCap (hw ▸ (m.contact contact).property)

theorem lower_only_not_in_upper (w : Fin A) (notAtCap : lower.finish w ≠ none)
    (i : Fin upper.levelCount) :
    lowerId w ∉ ((s.layer ((sweepStack m).upperLevel i)).slots.flatMap m.glue.slotInputs) ++
      ((s.layer ((sweepStack m).upperLevel i)).slots.flatMap m.glue.slotOutputs) := by
  rw [s.before, s.after, List.mem_append]
  exact fun h => h.elim (lower_only_absent m s w notAtCap i.castSucc)
    (lower_only_absent m s w notAtCap i.succ)

theorem upper_only_not_in_lower (w : Fin B) (notAtCap : upper.start w ≠ none)
    (i : Fin lower.levelCount) :
    m.upperId w ∉ ((s.layer ((sweepStack m).lowerLevel i)).slots.flatMap m.glue.slotInputs) ++
      ((s.layer ((sweepStack m).lowerLevel i)).slots.flatMap m.glue.slotOutputs) := by
  rw [s.before, s.after, List.mem_append]
  exact fun h => h.elim (upper_only_absent m s w notAtCap i.castSucc)
    (upper_only_absent m s w notAtCap i.succ)

end Silmaril.RuntimeWires.Proofs.PartialGluing
