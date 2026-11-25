module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Comparison
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Contacts
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Associator.Thms

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.CapClasses

open ProgressiveGraph ProgressiveGraph.Diagram.PartialVerticalMatch
open CollarAssociator (leftWire rightWire inputCap outputCap inputCap_val outputCap_val
  inputCap_x outputCap_x left_label right_label before_contact after_contact)

universe u v
variable {O : Type u} {S : Signature.{u,v} O}
variable {a b c d : CapProfile O}

def matching (p : FixedDrawing S a b) (q : FixedDrawing S b c) :
    p.drawing.OrderedVerticalMatch q.drawing where
  contact := p.output.symm.trans q.input
  label w := by
    let i := p.output.symm w
    have hw : p.output i = w := p.output.apply_symm_apply w
    change p.drawing.label w.val = q.drawing.label (q.input i).val
    rw [← hw, p.output_label, q.input_label]
  order w z := by
    let i := p.output.symm w
    let j := p.output.symm z
    have hw : p.output i = w := p.output.apply_symm_apply w
    have hz : p.output j = z := p.output.apply_symm_apply z
    change p.drawing.x w.val 1 < p.drawing.x z.val 1 ↔
      q.drawing.x (q.input i).val 0 < q.drawing.x (q.input j).val 0
    rw [← hw, ← hz, p.output_x, p.output_x, q.input_x, q.input_x]

theorem match_slot (p : FixedDrawing S a b) (q : FixedDrawing S b c) (i : Fin b.size) :
    (matching p q).contact (p.output i) = q.input i := by
  change q.input (p.output.symm (p.output i)) = _
  rw [Equiv.symm_apply_apply]

theorem match_x (p : FixedDrawing S a b) (q : FixedDrawing S b c) (w : Contact p.drawing) :
    p.drawing.x w.val 1 = q.drawing.x ((matching p q).contact w).val 0 := by
  obtain ⟨i, rfl⟩ := p.output.surjective w
  rw [match_slot, p.output_x, q.input_x]

noncomputable abbrev glue (p : FixedDrawing S a b) (q : FixedDrawing S b c) :
    FixedDrawing S a c where
  vertices := p.vertices + q.vertices
  wires := wireCount (matching p q).lowerJoin.glue q.drawing
  drawing := (matching p q).glue
  input := p.input.trans (inputCap (matching p q))
  output := q.output.trans (outputCap (matching p q))
  input_label i := by
    change (matching p q).glue.label (inputCap (matching p q) (p.input i)).val = _
    rw [inputCap_val, left_label, p.input_label]
  output_label i := by
    change (matching p q).glue.label (outputCap (matching p q) (q.output i)).val = _
    rw [outputCap_val, right_label, q.output_label]
  input_x i := (inputCap_x (matching p q) (p.input i)).trans (p.input_x i)
  output_x i := (outputCap_x (matching p q) (q.output i)).trans (q.output_x i)

theorem glue_straight_through (p : FixedDrawing S a b) (q : FixedDrawing S b c)
    (i : Fin a.size) (j : Fin b.size) (k : Fin c.size) (x : ℝ)
    (hp : (p.input i).val = (p.output j).val) (hq : (q.input j).val = (q.output k).val)
    (px : ∀ y, p.drawing.x (p.input i).val y = x)
    (qx : ∀ y, q.drawing.x (q.input j).val y = x) :
    ((glue p q).input i).val = ((glue p q).output k).val ∧
      ∀ y, (glue p q).drawing.x ((glue p q).input i).val y = x := by
  let m := matching p q
  have shared : leftWire m (p.input i).val = rightWire m (q.input j).val := by
    rw [hp]
    change lowerId (lowerId (p.output j).val) = m.upperJoin.upperId (q.input j).val
    rw [m.glue_matches_contact, match_slot]
  constructor
  · change (inputCap m (p.input i)).val = (outputCap m (q.output k)).val
    rw [inputCap_val, outputCap_val, shared, hq]
  · intro y
    change m.glue.x (inputCap m (p.input i)).val y = x
    rw [inputCap_val]
    by_cases below : y ≤ 1 / 4
    · have first : slabHeight 0 y ≤ 1 / 2 := by dsimp [slabHeight]; linarith
      have half : y ≤ 1 / 2 := by linarith
      rw [m.glue_eq_upperJoin, leftWire, m.upperJoin.glue_x_lower _ half,
        m.lowerJoin.glue_x_lower _ first]
      exact px _
    rw [shared]
    by_cases above : 1 / 2 ≤ y
    · rw [m.glue_eq_upperJoin, rightWire, m.upperJoin.glue_x_upper _ above]
      exact qx _
    have band : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2) := ⟨le_of_not_ge below, le_of_not_ge above⟩
    have collar := m.glue_x_in_collar (p.output j) band
    rw [match_slot] at collar
    change m.glue.x (rightWire m (q.input j).val) y = _ at collar
    rw [collar, ← hp, px, qx]
    unfold interpolate
    ring

section Boundary

variable {V W V' W' : ℕ}
variable {r : ProgressiveGraph.Diagram S V W .point} {s : ProgressiveGraph.Diagram S V' W' .point}

def renameInput (h : r.CapComparison s) : CollarAssociator.InputCap r ≃ CollarAssociator.InputCap s :=
  h.incidence.wire.subtypeEquiv fun w => by
    rw [h.incidence.start]
    cases r.start w <;> simp

def renameOutput (h : r.CapComparison s) : Contact r ≃ Contact s :=
  h.incidence.wire.subtypeEquiv fun w => by
    rw [h.incidence.finish]
    cases r.finish w <;> simp

end Boundary

theorem input_slot {p p' : FixedDrawing S a b} (h : p.drawing.CapComparison p'.drawing) (i : Fin a.size) :
    renameInput h (p.input i) = p'.input i := by
  apply Subtype.ext
  apply Decidable.byContradiction
  intro ne
  apply p'.drawing.input_boundary_separated ne (renameInput h (p.input i)).property (p'.input i).property
  exact (input_x h _ (p.input i).property).trans ((p.input_x i).trans (p'.input_x i).symm)

theorem output_slot {p p' : FixedDrawing S a b} (h : p.drawing.CapComparison p'.drawing) (i : Fin b.size) :
    renameOutput h (p.output i) = p'.output i := by
  apply Subtype.ext
  apply Decidable.byContradiction
  intro ne
  apply p'.drawing.output_boundary_separated ne (renameOutput h (p.output i)).property (p'.output i).property
  exact (output_x h _ (p.output i).property).trans ((p.output_x i).trans (p'.output_x i).symm)

theorem contact_transport {p p' : FixedDrawing S a b} {q q' : FixedDrawing S b c}
    (h : p.drawing.CapComparison p'.drawing) (k : q.drawing.CapComparison q'.drawing)
    (w : Contact p.drawing) :
    (matching p' q').contact (renameOutput h w) = renameInput k ((matching p q).contact w) := by
  obtain ⟨i, rfl⟩ := p.output.surjective w
  rw [output_slot h, match_slot, match_slot, input_slot k]

theorem match_ext {V W V' W' : ℕ} {r : ProgressiveGraph.Diagram S V W .point}
    {s : ProgressiveGraph.Diagram S V' W' .point} {m n : r.OrderedVerticalMatch s}
    (h : m.contact = n.contact) : m = n := by
  cases m
  cases n
  cases h
  rfl

theorem match_after (p : FixedDrawing S a b) (q : FixedDrawing S b c) (r : FixedDrawing S c d) :
    matching (glue p q) r = (matching p q).attachAfter (matching q r) := by
  apply match_ext
  apply Equiv.ext
  intro w
  obtain ⟨i, rfl⟩ := (glue p q).output.surjective w
  rw [match_slot]
  change r.input i = (CollarAssociator.after (matching p q) (matching q r)).contact
    (outputCap (matching p q) (q.output i))
  rw [after_contact, match_slot]

theorem match_before (p : FixedDrawing S a b) (q : FixedDrawing S b c) (r : FixedDrawing S c d) :
    matching p (glue q r) = (matching p q).attachBefore (matching q r) := by
  apply match_ext
  apply Equiv.ext
  intro w
  obtain ⟨i, rfl⟩ := p.output.surjective w
  rw [match_slot]
  change inputCap (matching q r) (q.input i) =
    (CollarAssociator.before (matching p q) (matching q r)).contact (p.output i)
  rw [before_contact, match_slot]

end Silmaril.RuntimeWires.Proofs.CapClasses
