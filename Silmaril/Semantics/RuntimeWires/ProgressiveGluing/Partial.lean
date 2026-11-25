module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PartialDefs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialCuts

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.PartialVerticalMatch

open Proofs.PartialGluing

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point}
variable {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)

/-- A fresh finite drawing obtained by splicing cap contacts and retaining
all remaining strands in their original slabs. -/
noncomputable def glue : ProgressiveGraph.Diagram S (L + R) (wireCount lower upper) .point :=
  assemble m

/-- The matching is an order isomorphism for the orders of the two caps. -/
theorem contact_order (a b : Contact lower) :
    lower.x a.val 1 < lower.x b.val 1 ↔ upper.x (m.contact a).val 0 < upper.x (m.contact b).val 0 := by
  rw [m.coordinate a, m.coordinate b]

theorem lowerId_injective : Function.Injective (lowerId (lower := lower) (upper := upper)) :=
  (numbering lower upper).injective.comp fromLower_injective

theorem upperId_injective : Function.Injective m.upperId :=
  (numbering lower upper).injective.comp (fromUpper_injective m)

theorem lowerId_shared (w : Contact lower) : lowerId w.val = m.sharedId w :=
  congrArg (numbering lower upper) (fromLower_shared w)

theorem upperId_shared (w : Contact lower) : m.upperId (m.contact w).val = m.sharedId w :=
  congrArg (numbering lower upper) (fromUpper_shared m w)

/-- The renamings identify exactly the pairs in the boundary matching. -/
theorem lowerId_eq_upperId {a : Fin A} {b : Fin B} :
    lowerId a = m.upperId b ↔ ∃ w : Contact lower, w.val = a ∧ (m.contact w).val = b :=
  (numbering lower upper).injective.eq_iff.trans (fromLower_eq_fromUpper m)


theorem glue_label_lower (w : Fin A) : m.glue.label (lowerId w) = lower.label w := by
  change wireLabel ((numbering lower upper).symm ((numbering lower upper) (fromLower w))) = _
  rw [Equiv.symm_apply_apply]
  exact label_fromLower w

theorem glue_label_upper (w : Fin B) : m.glue.label (m.upperId w) = upper.label w := by
  change wireLabel ((numbering lower upper).symm ((numbering lower upper) (m.fromUpper w))) = _
  rw [Equiv.symm_apply_apply]
  exact label_fromUpper m w

theorem glue_x_lower (w : Fin A) {y : ℝ} (below : y ≤ 1 / 2) :
    m.glue.x (lowerId w) y = lower.x w (slabHeight 0 y) := by
  change (jointWire m ((numbering lower upper).symm ((numbering lower upper) (fromLower w)))).x y = _
  rw [Equiv.symm_apply_apply]
  exact x_fromLower m w below

theorem glue_x_upper (w : Fin B) {y : ℝ} (above : 1 / 2 ≤ y) :
    m.glue.x (m.upperId w) y = upper.x w (slabHeight 1 y) := by
  change (jointWire m ((numbering lower upper).symm ((numbering lower upper) (m.fromUpper w)))).x y = _
  rw [Equiv.symm_apply_apply]
  exact x_fromUpper m w above

theorem glue_inputs_lower (v : Fin L) :
    m.glue.inputs (Fin.castAdd R v) = (lower.inputs v).map lowerId := by
  change List.ofFn (numbering lower upper ∘ jointInput m (Fin.castAdd R v)) = _
  rw [← List.map_ofFn, jointInput, jointPorts, Proofs.ProgressiveGluing.port_list_left]
  simp only [Diagram.inputs, List.map_ofFn, lowerId, Function.comp_def]

theorem glue_inputs_upper (v : Fin R) :
    m.glue.inputs (Fin.natAdd L v) = (upper.inputs v).map m.upperId := by
  change List.ofFn (numbering lower upper ∘ jointInput m (Fin.natAdd L v)) = _
  rw [← List.map_ofFn, jointInput, jointPorts, Proofs.ProgressiveGluing.port_list_right]
  simp only [Diagram.inputs, List.map_ofFn, upperId, Function.comp_def]

theorem glue_outputs_lower (v : Fin L) :
    m.glue.outputs (Fin.castAdd R v) = (lower.outputs v).map lowerId := by
  change List.ofFn (numbering lower upper ∘ jointOutput m (Fin.castAdd R v)) = _
  rw [← List.map_ofFn, jointOutput, jointPorts, Proofs.ProgressiveGluing.port_list_left]
  simp only [Diagram.outputs, List.map_ofFn, lowerId, Function.comp_def]

theorem glue_outputs_upper (v : Fin R) :
    m.glue.outputs (Fin.natAdd L v) = (upper.outputs v).map m.upperId := by
  change List.ofFn (numbering lower upper ∘ jointOutput m (Fin.natAdd L v)) = _
  rw [← List.map_ofFn, jointOutput, jointPorts, Proofs.ProgressiveGluing.port_list_right]
  simp only [Diagram.outputs, List.map_ofFn, upperId, Function.comp_def]

theorem glue_height_lower (v : Fin L) :
    m.glue.vertexHeight (Fin.castAdd R v) = halfHeight 0 (lower.vertexHeight v) :=
  Proofs.ProgressiveGluing.height_left v

theorem glue_height_upper (v : Fin R) :
    m.glue.vertexHeight (Fin.natAdd L v) = halfHeight 1 (upper.vertexHeight v) :=
  Proofs.ProgressiveGluing.height_right v

theorem join_regular : m.glue.Regular (1 / 2) :=
  Proofs.PartialGluing.join_regular m

/-- The wires active at the actual splice are exactly the shared IDs. -/
theorem crosses_join_iff (z : Fin (wireCount lower upper)) :
    m.glue.crosses z (1 / 2) ↔ ∃ w : Contact lower, m.sharedId w = z :=
  Proofs.PartialGluing.crosses_join_iff m z

/-- Ordered cap contacts give the exact ordered cut at the splice. -/
theorem ordered_join {ws : List (Contact lower)} (exact_contacts : ∀ w, w ∈ ws)
    (ordered : ws.Pairwise (fun a b => lower.x a.val 1 < lower.x b.val 1)) :
    m.glue.OrderedCut (1 / 2) (ws.map m.sharedId) :=
  Proofs.PartialGluing.ordered_join m exact_contacts ordered

/-- Both names of each contact give the very same ordered list of fresh IDs. -/
theorem join_renamings (ws : List (Contact lower)) :
    ws.map (fun w => lowerId (upper := upper) w.val) = ws.map m.sharedId ∧
      ws.map (fun w => m.upperId (m.contact w).val) = ws.map m.sharedId :=
  ⟨congrArg (fun f => ws.map f) (funext m.lowerId_shared),
    congrArg (fun f => ws.map f) (funext m.upperId_shared)⟩

/-- Every cut below the splice retains its full ordered list after renaming. -/
theorem cut_lower {h : ℝ} {ws : List (Fin A)} (below : h < 1) (cut : lower.OrderedCut h ws) :
    m.glue.OrderedCut (halfHeight 0 h) (ws.map lowerId) :=
  Proofs.PartialGluing.cut_lower m below cut

/-- Every cut above the splice retains its full ordered list after renaming. -/
theorem cut_upper {h : ℝ} {ws : List (Fin B)} (above : 0 < h) (cut : upper.OrderedCut h ws) :
    m.glue.OrderedCut (halfHeight 1 h) (ws.map m.upperId) :=
  Proofs.PartialGluing.cut_upper m above cut

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.PartialVerticalMatch
