module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Topological
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialAssembly

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.OperandAmbient

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.PartialGluing

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V A B : ℕ}
variable {d : ProgressiveGraph.Diagram S V A .point} {e : ProgressiveGraph.Diagram S V B .point}
variable {f : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)} (p : d.AmbientFrame e f)

def bottom : {w // d.start w = none} ≃ {w // e.start w = none} :=
  p.rename.subtypeEquiv fun w => by rw [p.start]

def top : Contact d ≃ Contact e :=
  p.rename.subtypeEquiv fun w => by rw [p.finish]

def lowerOnly : LowerOnly d ≃ LowerOnly e :=
  p.rename.subtypeEquiv fun w => by rw [p.finish]

def upperOnly : UpperOnly d ≃ UpperOnly e :=
  p.rename.subtypeEquiv fun w => by rw [p.start]

theorem lower_eq (w : Fin A) : e.lower (p.rename w) = d.lower w := by
  simp only [ProgressiveGraph.Diagram.lower, p.heights, p.start]

theorem upper_eq (w : Fin A) : e.upper (p.rename w) = d.upper w := by
  simp only [ProgressiveGraph.Diagram.upper, p.heights, p.finish]

theorem bottom_x (w : {w // d.start w = none}) (fixed : ∀ x : ℝ, f (x, 0) = (x, 0)) :
    e.x (bottom p w).val 0 = d.x w.val 0 := by
  have lo : d.lower w.val = 0 := by simp [ProgressiveGraph.Diagram.lower, endpointHeight, w.property]
  have cover : d.covers w.val 0 := ⟨lo.le, lo ▸ (d.wire w.val).increasing.le⟩
  have h := p.wire w.val 0 cover
  rw [fixed] at h
  exact (congrArg Prod.fst h).symm

theorem top_x (w : Contact d) (fixed : ∀ x : ℝ, f (x, 1) = (x, 1)) :
    e.x (top p w).val 1 = d.x w.val 1 := by
  have hi : d.upper w.val = 1 := by simp [ProgressiveGraph.Diagram.upper, endpointHeight, w.property]
  have cover : d.covers w.val 1 := ⟨hi ▸ (d.wire w.val).increasing.le, hi.ge⟩
  have h := p.wire w.val 1 cover
  rw [fixed] at h
  exact (congrArg Prod.fst h).symm

section Two

variable {R C D : ℕ}
variable {b : ProgressiveGraph.Diagram S R C .point} {c : ProgressiveGraph.Diagram S R D .point}
variable {g : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)} (q : b.AmbientFrame c g)
variable (m : d.PartialVerticalMatch b)

/-- Transport the actual typed cap bijection through the wire renamings. -/
def transport (fixTop : ∀ x : ℝ, f (x, 1) = (x, 1)) (fixBottom : ∀ x : ℝ, g (x, 0) = (x, 0)) :
    e.PartialVerticalMatch c where
  contact := (top p).symm.trans (m.contact.trans (bottom q))
  label z := by
    let w := (top p).symm z
    have eq := (top p).apply_symm_apply z
    change e.label z.val = c.label (bottom q (m.contact w)).val
    rw [← eq]
    exact (p.label w.val).trans ((m.label w).trans (q.label (m.contact w).val).symm)
  coordinate z := by
    let w := (top p).symm z
    have eq := (top p).apply_symm_apply z
    change e.x z.val 1 = c.x (bottom q (m.contact w)).val 0
    rw [← eq]
    exact (top_x p w fixTop).trans ((m.coordinate w).trans (bottom_x q (m.contact w) fixBottom).symm)

variable (fixTop : ∀ x : ℝ, f (x, 1) = (x, 1)) (fixBottom : ∀ x : ℝ, g (x, 0) = (x, 0))

theorem contact_renamed (z : Contact d) :
    (transport p q m fixTop fixBottom).contact (top p z) = bottom q (m.contact z) := by
  change bottom q (m.contact ((top p).symm (top p z))) = _
  rw [Equiv.symm_apply_apply]

def wireRename : WireId d b ≃ WireId e c :=
  Equiv.sumCongr (lowerOnly p) (Equiv.sumCongr (top p) (upperOnly q))

theorem lowerPart_renamed (z : WireId d b) :
    lowerPart (wireRename p q z) = (lowerPart z).map p.rename := by
  rcases z with z | (z | z) <;> rfl

theorem upperPart_renamed (z : WireId d b) :
    (transport p q m fixTop fixBottom).upperPart (wireRename p q z) =
      (m.upperPart z).map q.rename := by
  rcases z with z | (z | z)
  · rfl
  · change some ((transport p q m fixTop fixBottom).contact (top p z)).val = _
    rw [contact_renamed]
    rfl
  · rfl

theorem fromLower_renamed (w : Fin A) :
    wireRename p q (fromLower (upper := b) w) = fromLower (upper := c) (p.rename w) := by
  symm
  apply (lower_exists (upper := c)).mpr
  simp only [lowerPart_renamed, lowerPart_fromLower, Option.map_some]

theorem fromUpper_renamed (w : Fin C) :
    wireRename p q (m.fromUpper w) = (transport p q m fixTop fixBottom).fromUpper (q.rename w) := by
  symm
  apply (upper_exists (transport p q m fixTop fixBottom)).mpr
  simp only [upperPart_renamed, upperPart_fromUpper, Option.map_some]

noncomputable def gluedRename : Fin (wireCount d b) ≃ Fin (wireCount e c) :=
  (numbering d b).symm.trans ((wireRename p q).trans (numbering e c))

theorem lowerId_renamed (w : Fin A) :
    gluedRename p q (lowerId (upper := b) w) = lowerId (upper := c) (p.rename w) := by
  change (numbering e c) (wireRename p q ((numbering d b).symm ((numbering d b) (fromLower w)))) = _
  rw [Equiv.symm_apply_apply, fromLower_renamed]
  rfl

theorem upperId_renamed (w : Fin C) :
    gluedRename p q (m.upperId w) = (transport p q m fixTop fixBottom).upperId (q.rename w) := by
  change (numbering e c) (wireRename p q ((numbering d b).symm ((numbering d b) (m.fromUpper w)))) = _
  rw [Equiv.symm_apply_apply, fromUpper_renamed p q m fixTop fixBottom]
  rfl

end Two
end Silmaril.RuntimeWires.Proofs.OperandAmbient
