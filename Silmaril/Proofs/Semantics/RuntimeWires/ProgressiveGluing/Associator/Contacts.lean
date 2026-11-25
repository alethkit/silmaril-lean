module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Collar
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Collar
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarJoins
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialAssembly
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Partial
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Proofs.CollarAssociator

open ProgressiveGraph
open ProgressiveGraph.Diagram (OrderedVerticalMatch PartialVerticalMatch)
open ProgressiveGraph.Diagram.PartialVerticalMatch
open PartialGluing (assemble wireStart start_on_cap)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L M A B : ℕ}
variable {d : ProgressiveGraph.Diagram S L A .point} {e : ProgressiveGraph.Diagram S M B .point}

abbrev InputCap (d : ProgressiveGraph.Diagram S L A .point) := {w : Fin A // d.start w = none}

theorem start_lower (j : d.PartialVerticalMatch e) (a : Fin A) :
    j.glue.start (lowerId (upper := e) a) = (d.start a).map (Fin.castAdd M) := by
  change wireStart ((numbering d e).symm ((numbering d e) (fromLower a))) = _
  rw [Equiv.symm_apply_apply]
  unfold fromLower
  split <;> rfl

theorem input_exists (j : d.PartialVerticalMatch e) (w : InputCap j.glue) :
    ∃ a : InputCap d, lowerId (upper := e) a.val = w.val := by
  let n := numbering d e
  have h : wireStart (n.symm w.val) = none := w.property
  obtain ⟨a, id, cap⟩ := start_on_cap h
  exact ⟨⟨a, cap⟩, (congrArg n id).trans (n.apply_symm_apply w.val)⟩

noncomputable def lowerCapEquiv (j : d.PartialVerticalMatch e) : InputCap d ≃ InputCap j.glue :=
  Equiv.ofBijective (fun a => ⟨lowerId (upper := e) a.val, by rw [start_lower, a.property]; rfl⟩)
    ⟨fun _ _ eq => Subtype.ext ((lowerId_injective (lower := d) (upper := e)) (congrArg Subtype.val eq)),
     fun w => by obtain ⟨a, id⟩ := input_exists j w; exact ⟨a, Subtype.ext id⟩⟩

theorem lowerCap_x (j : d.PartialVerticalMatch e) (a : InputCap d) :
    j.glue.x (lowerCapEquiv j a).val 0 = d.x a.val 0 := by
  change j.glue.x (lowerId (upper := e) a.val) 0 = _
  simpa only [show slabHeight 0 0 = 0 by norm_num [slabHeight]] using j.glue_x_lower a.val (y := 0) (by norm_num)

variable (m : d.OrderedVerticalMatch e)

theorem sameGlue : m.glue = m.upperJoin.glue := by rfl

@[expose] noncomputable def leftWire (a : Fin A) : Fin (wireCount m.lowerJoin.glue e) :=
  lowerId (upper := e) (lowerId (upper := m.collar) a)

@[expose] noncomputable def rightWire (b : Fin B) : Fin (wireCount m.lowerJoin.glue e) :=
  m.upperJoin.upperId b

noncomputable def inputCap : InputCap d ≃ InputCap m.glue :=
  (lowerCapEquiv m.lowerJoin).trans (lowerCapEquiv m.upperJoin) |>.trans
    (Equiv.subtypeEquivRight (fun _ => by rw [sameGlue m]))

noncomputable def outputCap : Contact e ≃ Contact m.glue :=
  (ProgressiveGluing.upperCapEquiv m.upperJoin).trans
    (Equiv.subtypeEquivRight (fun _ => by rw [sameGlue m]))

theorem inputCap_val (a : InputCap d) : (inputCap m a).val = leftWire m a.val := by rfl

theorem outputCap_val (b : Contact e) : (outputCap m b).val = rightWire m b.val := by rfl

theorem inputCap_x (a : InputCap d) : m.glue.x (inputCap m a).val 0 = d.x a.val 0 := by
  rw [inputCap_val, sameGlue m]
  exact (lowerCap_x m.upperJoin (lowerCapEquiv m.lowerJoin a)).trans (lowerCap_x m.lowerJoin a)

theorem outputCap_x (b : Contact e) : m.glue.x (outputCap m b).val 1 = e.x b.val 1 := by
  rw [outputCap_val, sameGlue m]
  exact ProgressiveGluing.upperCap_x m.upperJoin b

theorem left_label (a : Fin A) : m.glue.label (leftWire m a) = d.label a := by
  rw [sameGlue m]
  exact (m.upperJoin.glue_label_lower _).trans (m.lowerJoin.glue_label_lower a)

theorem right_label (b : Fin B) : m.glue.label (rightWire m b) = e.label b := by
  rw [sameGlue m]
  exact m.upperJoin.glue_label_upper b

section Triple

variable {R C : ℕ} {f : ProgressiveGraph.Diagram S R C .point}
variable (n : e.OrderedVerticalMatch f)

/-- The second local matching, inherited at the actual output cap of the first glued pair. -/
noncomputable def after : m.glue.OrderedVerticalMatch f where
  contact := (outputCap m).symm.trans n.contact
  label b := by
    let a := (outputCap m).symm b
    have h : outputCap m a = b := (outputCap m).apply_symm_apply b
    change m.glue.label b.val = f.label (n.contact a).val
    rw [← h, outputCap_val, right_label]
    exact n.label a
  order a b := by
    let i := (outputCap m).symm a
    let j := (outputCap m).symm b
    change m.glue.x a.val 1 < m.glue.x b.val 1 ↔ f.x (n.contact i).val 0 < f.x (n.contact j).val 0
    rw [← (outputCap m).apply_symm_apply a, ← (outputCap m).apply_symm_apply b, outputCap_x, outputCap_x]
    exact n.order i j

/-- The first local matching, inherited at the actual input cap of the second glued pair. -/
noncomputable def before : d.OrderedVerticalMatch n.glue where
  contact := m.contact.trans (inputCap n)
  label a := by
    change d.label a.val = n.glue.label (inputCap n (m.contact a)).val
    rw [inputCap_val, left_label]
    exact m.label a
  order a b := by
    change d.x a.val 1 < d.x b.val 1 ↔
      n.glue.x (inputCap n (m.contact a)).val 0 < n.glue.x (inputCap n (m.contact b)).val 0
    rw [inputCap_x, inputCap_x]
    exact m.order a b

theorem after_contact (b : Contact e) : (after m n).contact (outputCap m b) = n.contact b := by
  change n.contact ((outputCap m).symm (outputCap m b)) = _
  rw [Equiv.symm_apply_apply]

theorem before_contact (a : Contact d) : (before m n).contact a = inputCap n (m.contact a) := by rfl

end Triple
end Silmaril.RuntimeWires.Proofs.CollarAssociator
