module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PartialDefs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveNullarySlide.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialCuts
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.NullaryGlueLower

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

theorem glue_finish_upper (w : Fin B) :
    m.glue.finish (m.upperId w) = (upper.finish w).map (Fin.natAdd L) :=
  finish_upper_id m w

theorem glue_output_cap_exists {z : Fin (wireCount lower upper)} (h : m.glue.finish z = none) :
    ∃ w, upper.finish w = none ∧ m.upperId w = z :=
  finish_cap_exists m h

theorem glue_covered_lower {w : Fin (wireCount lower upper)} {y : ℝ}
    (hy : y ≤ 1 / 2) (cover : m.glue.covers w y) :
    ∃ a, (lowerId (upper := upper) a) = w ∧ lower.covers a (slabHeight 0 y) :=
  covered_assemble_lower m hy cover

theorem glue_covered_upper {w : Fin (wireCount lower upper)} {y : ℝ}
    (hy : 1 / 2 ≤ y) (cover : m.glue.covers w y) :
    ∃ b, m.upperId b = w ∧ upper.covers b (slabHeight 1 y) :=
  covered_assemble_upper m hy cover

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

theorem glue_vertexX_lower (v : Fin L) :
    m.glue.vertexX (Fin.castAdd R v) = lower.vertexX v :=
  Proofs.ProgressiveGluing.x_left v

theorem glue_vertexX_upper (v : Fin R) :
    m.glue.vertexX (Fin.natAdd L v) = upper.vertexX v :=
  Proofs.ProgressiveGluing.x_right v

theorem glue_generator_lower (v : Fin L) :
    m.glue.generator (Fin.castAdd R v) = lower.generator v :=
  Proofs.ProgressiveGluing.generator_left v

theorem glue_generator_upper (v : Fin R) :
    m.glue.generator (Fin.natAdd L v) = upper.generator v :=
  Proofs.ProgressiveGluing.generator_right v

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

section NullarySlide

variable {v : Fin R} (move : upper.NullarySlide v)

/-- The original matching, read at the upper slide frame. The lower
operand, the cap coordinates, and the matched wire IDs are fixed. -/
def matchAtUpper {h : ℝ} (hh : h ∈ Set.Icc move.bottom move.top) :
    lower.PartialVerticalMatch (move.atHeight h hh) :=
  Proofs.PartialGluing.matchAtUpperHeight m move hh

theorem matchAtUpper_contact {h : ℝ} (hh : h ∈ Set.Icc move.bottom move.top) :
    (m.matchAtUpper move hh).contact = m.contact := by rfl

theorem matchAtUpper_ids {h : ℝ} (hh : h ∈ Set.Icc move.bottom move.top) (a : Fin A) (b : Fin B) :
    lowerId (lower := lower) (upper := (move.atHeight h hh)) a =
      lowerId (lower := lower) (upper := upper) a ∧
    (m.matchAtUpper move hh).upperId b = m.upperId b := by
  exact ⟨rfl, rfl⟩

/-- Lift a nullary slide through a fixed lower attachment. -/
noncomputable def liftUpperSlide : m.glue.NullarySlide (Fin.natAdd L v) :=
  Proofs.PartialGluing.liftUpper m move

theorem liftUpperSlide_bottom : (m.liftUpperSlide move).bottom = halfHeight 1 move.bottom := by rfl

theorem liftUpperSlide_top : (m.liftUpperSlide move).top = halfHeight 1 move.top := by rfl

theorem liftUpperSlide_heightAt (t : Diagram.NullarySlide.Time) :
    (m.liftUpperSlide move).heightAt t = halfHeight 1 (move.heightAt t) :=
  Proofs.PartialGluing.liftUpper_heightAt m move t

/-- The lifted frames are the actual glued drawings of the original frames. -/
theorem liftUpperSlide_frame (t : Diagram.NullarySlide.Time) :
    (m.liftUpperSlide move).frame t = (m.matchAtUpper move (move.height_mem t)).glue :=
  Proofs.PartialGluing.liftUpper_frame m move t

end NullarySlide

section NullarySlideLower

variable {v : Fin L} (move : lower.NullarySlide v)

/-- The original matching, read at the lower slide frame. -/
def matchAtLower {h : ℝ} (hh : h ∈ Set.Icc move.bottom move.top) :
    (move.atHeight h hh).PartialVerticalMatch upper :=
  Proofs.PartialGluing.matchAtLowerHeight m move hh

theorem matchAtLower_contact {h : ℝ} (hh : h ∈ Set.Icc move.bottom move.top) :
    (m.matchAtLower move hh).contact = m.contact := by rfl

theorem matchAtLower_ids {h : ℝ} (hh : h ∈ Set.Icc move.bottom move.top) (a : Fin A) (b : Fin B) :
    lowerId (lower := (move.atHeight h hh)) (upper := upper) a =
      lowerId (lower := lower) (upper := upper) a ∧
    (m.matchAtLower move hh).upperId b = m.upperId b := by
  exact ⟨rfl, rfl⟩

/-- Lift a nullary slide through a fixed upper attachment. -/
noncomputable def liftLowerSlide : m.glue.NullarySlide (Fin.castAdd R v) :=
  Proofs.PartialGluing.liftLower m move

theorem liftLowerSlide_bottom : (m.liftLowerSlide move).bottom = halfHeight 0 move.bottom := by rfl

theorem liftLowerSlide_top : (m.liftLowerSlide move).top = halfHeight 0 move.top := by rfl

theorem liftLowerSlide_heightAt (t : Diagram.NullarySlide.Time) :
    (m.liftLowerSlide move).heightAt t = halfHeight 0 (move.heightAt t) :=
  Proofs.PartialGluing.liftLower_heightAt m move t

theorem liftLowerSlide_frame (t : Diagram.NullarySlide.Time) :
    (m.liftLowerSlide move).frame t = (m.matchAtLower move (move.height_mem t)).glue :=
  Proofs.PartialGluing.liftLower_frame m move t

end NullarySlideLower

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.PartialVerticalMatch
