module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Drawing
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Matching
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Wires

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.Whiskering

open ProgressiveGraph ProgressiveGraph.Diagram.PartialVerticalMatch
open HorizontalPlacement (adjoin placed slots contacts_active contacts_idle)
open CapClasses (matching match_slot glue)
open CollarAssociator (leftWire rightWire wire_contact wire_cases descend descend_left descend_right)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c : FixedCap S}
variable (s : ActiveStrip) (idle : FixedCap S)
variable (p : FixedDrawing S a.profile b.profile) (q : FixedDrawing S b.profile c.profile)

abbrev wideMatch := matching (placed s idle p) (placed s idle q)

abbrev stackThenPlace := placed s idle (a := a) (b := c) (glue p q)

abbrev placeThenStack := glue (placed s idle p) (placed s idle q)

local notation "I" => idle.profile.size
local notation "m" => matching p q
local notation "n" => wideMatch s idle p q

theorem output_active (i : Fin b.profile.size) :
    ((placed s idle p).output ((slots s b idle).symm (.inl i))).val =
      Fin.castAdd I (p.output i).val :=
  contacts_active _ _ p.output i

theorem input_active (i : Fin b.profile.size) :
    ((placed s idle q).input ((slots s b idle).symm (.inl i))).val =
      Fin.castAdd I (q.input i).val :=
  contacts_active _ _ q.input i

theorem output_idle (j : Fin I) :
    ((placed s idle p).output ((slots s b idle).symm (.inr j))).val = Fin.natAdd p.wires j :=
  contacts_idle _ _ p.output j

theorem input_idle (j : Fin I) :
    ((placed s idle q).input ((slots s b idle).symm (.inr j))).val = Fin.natAdd q.wires j :=
  contacts_idle _ _ q.input j

theorem active_splice (i : Fin b.profile.size) :
    leftWire n (Fin.castAdd I (p.output i).val) =
      rightWire n (Fin.castAdd I (q.input i).val) := by
  have eq := wire_contact n ((placed s idle p).output ((slots s b idle).symm (.inl i)))
  rw [match_slot, output_active, input_active] at eq
  exact eq

theorem idle_splice (i : Fin I) :
    leftWire n (Fin.natAdd p.wires i) = rightWire n (Fin.natAdd q.wires i) := by
  have eq := wire_contact n ((placed s idle p).output ((slots s b idle).symm (.inr i)))
  rw [match_slot, output_idle, input_idle] at eq
  exact eq

def fromActive : Fin (glue p q).wires → Fin (placeThenStack s idle p q).wires :=
  descend m (leftWire n ∘ Fin.castAdd I) (rightWire n ∘ Fin.castAdd I)

theorem active_lower (i : Fin p.wires) :
    fromActive s idle p q (leftWire m i) = leftWire n (Fin.castAdd I i) :=
  descend_left _ _ _ i

theorem active_upper (i : Fin q.wires) :
    fromActive s idle p q (rightWire m i) = rightWire n (Fin.castAdd I i) := by
  apply descend_right
  intro k
  obtain ⟨j, rfl⟩ := p.output.surjective k
  change leftWire n (Fin.castAdd I (p.output j).val) =
    rightWire n (Fin.castAdd I ((matching p q).contact (p.output j)).val)
  rw [match_slot]
  exact active_splice s idle p q j

def toLower : Fin (p.wires + I) → Fin ((glue p q).wires + I) :=
  Fin.append (Fin.castAdd I ∘ leftWire m) (Fin.natAdd (glue p q).wires)

def toUpper : Fin (q.wires + I) → Fin ((glue p q).wires + I) :=
  Fin.append (Fin.castAdd I ∘ rightWire m) (Fin.natAdd (glue p q).wires)

theorem to_agree (k : Contact (placed s idle p).drawing) :
    toLower idle p q k.val = toUpper idle p q ((wideMatch s idle p q).contact k).val := by
  obtain ⟨i, rfl⟩ := (placed s idle p).output.surjective k
  rw [match_slot]
  obtain ⟨slot, rfl⟩ := (slots s b idle).symm.surjective i
  cases slot with
  | inl j =>
    rw [output_active, input_active, toLower, toUpper, Fin.append_left, Fin.append_left]
    change Fin.castAdd I (leftWire m (p.output j).val) = Fin.castAdd I (rightWire m (q.input j).val)
    exact congrArg (Fin.castAdd I) ((wire_contact m (p.output j)).trans
      (congrArg (fun k => rightWire m k.val) (match_slot p q j)))
  | inr j => rw [output_idle, input_idle, toLower, toUpper, Fin.append_right, Fin.append_right]

def back : Fin (placeThenStack s idle p q).wires → Fin ((glue p q).wires + I) :=
  descend n (toLower idle p q) (toUpper idle p q)

theorem back_lower (i : Fin (p.wires + I)) :
    back s idle p q (leftWire n i) = toLower idle p q i :=
  descend_left _ _ _ i

theorem back_upper (i : Fin (q.wires + I)) :
    back s idle p q (rightWire n i) = toUpper idle p q i :=
  descend_right _ _ _ (to_agree s idle p q) i

def forward : Fin ((glue p q).wires + I) → Fin (placeThenStack s idle p q).wires :=
  Fin.append (fromActive s idle p q) (leftWire n ∘ Fin.natAdd p.wires)

theorem forward_active_lower (i : Fin p.wires) :
    forward s idle p q (Fin.castAdd I (leftWire m i)) = leftWire n (Fin.castAdd I i) := by
  rw [forward, Fin.append_left, active_lower]

theorem forward_active_upper (i : Fin q.wires) :
    forward s idle p q (Fin.castAdd I (rightWire m i)) = rightWire n (Fin.castAdd I i) := by
  rw [forward, Fin.append_left, active_upper]

theorem forward_idle_lower (i : Fin I) :
    forward s idle p q (Fin.natAdd (glue p q).wires i) = leftWire n (Fin.natAdd p.wires i) :=
  Fin.append_right _ _ i

theorem forward_idle_upper (i : Fin I) :
    forward s idle p q (Fin.natAdd (glue p q).wires i) = rightWire n (Fin.natAdd q.wires i) :=
  (forward_idle_lower s idle p q i).trans (idle_splice s idle p q i)

def wireEquiv : Fin ((glue p q).wires + I) ≃ Fin (placeThenStack s idle p q).wires where
  toFun := forward s idle p q
  invFun := back s idle p q
  left_inv w := by
    induction w using Fin.addCases with
    | left w =>
      rcases wire_cases m w with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [forward_active_lower, back_lower, toLower, Fin.append_left]
        rfl
      · rw [forward_active_upper, back_upper, toUpper, Fin.append_left]
        rfl
    | right i => rw [forward_idle_lower, back_lower, toLower, Fin.append_right]
  right_inv w := by
    rcases wire_cases n w with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · induction i using Fin.addCases with
      | left j => rw [back_lower, toLower, Fin.append_left]; exact forward_active_lower s idle p q j
      | right j => rw [back_lower, toLower, Fin.append_right]; exact forward_idle_lower s idle p q j
    · induction i using Fin.addCases with
      | left j => rw [back_upper, toUpper, Fin.append_left]; exact forward_active_upper s idle p q j
      | right j => rw [back_upper, toUpper, Fin.append_right]; exact forward_idle_upper s idle p q j

end Silmaril.RuntimeWires.Proofs.Whiskering
