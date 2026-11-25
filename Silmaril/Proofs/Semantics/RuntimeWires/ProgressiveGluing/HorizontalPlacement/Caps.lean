module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Geometry
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Sum.Basic

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.HorizontalPlacement

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

def beside (a b : FixedCap S) : FixedCap S where
  profile :=
    { size := a.profile.size + b.profile.size
      label := Fin.append a.profile.label b.profile.label
      x := Fin.append (fun i => ActiveStrip.left.place (a.profile.x i))
        (fun j => ActiveStrip.right.place (b.profile.x j))
      ordered := by
        intro i j lt
        induction i using Fin.addCases with
        | left i =>
          induction j using Fin.addCases with
          | left j => simpa only [Fin.append_left] using
              place_strict .left (a.profile.ordered (show i < j from lt))
          | right j => simpa only [Fin.append_left, Fin.append_right] using
              left_before_right (a.inside i).2 (b.inside j).1
        | right i =>
          induction j using Fin.addCases with
          | left j =>
            change a.profile.size + i.val < j.val at lt
            omega
          | right j =>
            change a.profile.size + i.val < a.profile.size + j.val at lt
            simpa only [Fin.append_right] using
              place_strict .right (b.profile.ordered (show i < j from Nat.lt_of_add_lt_add_left lt)) }
  inside i := by
    induction i using Fin.addCases with
    | left i => simpa only [Fin.append_left] using place_inside .left (a.inside i)
    | right i => simpa only [Fin.append_right] using place_inside .right (b.inside i)

def adjoin (s : ActiveStrip) (active idle : FixedCap S) : FixedCap S :=
  match s with
  | .left => beside active idle
  | .right => beside idle active

/-- Read the cap in left-to-right order and distinguish which operand
supplies the contact. Wire numbering is kept separate from this order. -/
def slots (s : ActiveStrip) (active idle : FixedCap S) :
    Fin (adjoin s active idle).profile.size ≃ Fin active.profile.size ⊕ Fin idle.profile.size :=
  match s with
  | .left => finSumFinEquiv.symm
  | .right => finSumFinEquiv.symm.trans (Equiv.sumComm _ _)

theorem active_slot_label (s : ActiveStrip) (a idle : FixedCap S) (i : Fin a.profile.size) :
    (adjoin s a idle).profile.label ((slots s a idle).symm (.inl i)) = a.profile.label i := by
  cases s
  · exact Fin.append_left _ _ _
  · exact Fin.append_right _ _ _

theorem idle_slot_label (s : ActiveStrip) (a idle : FixedCap S) (i : Fin idle.profile.size) :
    (adjoin s a idle).profile.label ((slots s a idle).symm (.inr i)) = idle.profile.label i := by
  cases s
  · exact Fin.append_right _ _ _
  · exact Fin.append_left _ _ _

theorem active_slot_x (s : ActiveStrip) (a idle : FixedCap S) (i : Fin a.profile.size) :
    (adjoin s a idle).profile.x ((slots s a idle).symm (.inl i)) = s.place (a.profile.x i) := by
  cases s
  · exact Fin.append_left (fun j => ActiveStrip.left.place (a.profile.x j))
      (fun j => ActiveStrip.right.place (idle.profile.x j)) i
  · exact Fin.append_right (fun j => ActiveStrip.left.place (idle.profile.x j))
      (fun j => ActiveStrip.right.place (a.profile.x j)) i

theorem idle_slot_x (s : ActiveStrip) (a idle : FixedCap S) (i : Fin idle.profile.size) :
    (adjoin s a idle).profile.x ((slots s a idle).symm (.inr i)) = s.opposite.place (idle.profile.x i) := by
  cases s
  · exact Fin.append_right (fun j => ActiveStrip.left.place (a.profile.x j))
      (fun j => ActiveStrip.right.place (idle.profile.x j)) i
  · exact Fin.append_left (fun j => ActiveStrip.left.place (idle.profile.x j))
      (fun j => ActiveStrip.right.place (a.profile.x j)) i

section Contacts

variable {V W I : ℕ} {old : Fin W → Option (Fin V)} {new : Fin (W + I) → Option (Fin V)}
variable (onActive : ∀ w, new (Fin.castAdd I w) = old w)
variable (onIdle : ∀ j, new (Fin.natAdd W j) = none)

def contactVal : {w : Fin W // old w = none} ⊕ Fin I → {w // new w = none}
  | .inl w => ⟨Fin.castAdd I w.val, (onActive w.val).trans w.property⟩
  | .inr j => ⟨Fin.natAdd W j, onIdle j⟩

theorem contactVal_wire (w : {w : Fin W // old w = none} ⊕ Fin I) :
    (contactVal onActive onIdle w).val = finSumFinEquiv (w.map Subtype.val id) := by
  cases w <;> rfl

def contactEquiv : ({w : Fin W // old w = none} ⊕ Fin I) ≃ {w // new w = none} :=
  Equiv.ofBijective (contactVal onActive onIdle) ⟨by
    intro w z eq
    have ids := congrArg Subtype.val eq
    rw [contactVal_wire, contactVal_wire] at ids
    exact (Sum.map_injective.mpr ⟨Subtype.val_injective, Function.injective_id⟩)
      (finSumFinEquiv.injective ids), by
    rintro ⟨w, hw⟩
    induction w using Fin.addCases with
    | left i => exact ⟨.inl ⟨i, (onActive i).symm.trans hw⟩, Subtype.ext rfl⟩
    | right j => exact ⟨.inr j, Subtype.ext rfl⟩⟩

end Contacts

section OrderedContacts

variable {V W : ℕ} {s : ActiveStrip} {active idle : FixedCap S}
variable {old : Fin W → Option (Fin V)}
variable {new : Fin (W + idle.profile.size) → Option (Fin V)}
variable (onActive : ∀ w, new (Fin.castAdd idle.profile.size w) = old w)
variable (onIdle : ∀ j, new (Fin.natAdd W j) = none)
variable (cap : Fin active.profile.size ≃ {w : Fin W // old w = none})

def contacts : Fin (adjoin s active idle).profile.size ≃ {w // new w = none} :=
  (slots s active idle).trans ((cap.sumCongr (Equiv.refl _)).trans (contactEquiv onActive onIdle))

theorem contacts_active (i : Fin active.profile.size) :
    (contacts (s := s) (idle := idle) onActive onIdle cap ((slots s active idle).symm (.inl i))).val =
      Fin.castAdd idle.profile.size (cap i).val := by
  change ((contactEquiv onActive onIdle) ((cap.sumCongr (Equiv.refl (Fin idle.profile.size)))
    ((slots s active idle) ((slots s active idle).symm (.inl i))))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem contacts_idle (i : Fin idle.profile.size) :
    (contacts (s := s) (idle := idle) onActive onIdle cap ((slots s active idle).symm (.inr i))).val =
      Fin.natAdd W i := by
  change ((contactEquiv onActive onIdle) ((cap.sumCongr (Equiv.refl (Fin idle.profile.size)))
    ((slots s active idle) ((slots s active idle).symm (.inr i))))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

end OrderedContacts

end Silmaril.RuntimeWires.Proofs.HorizontalPlacement
