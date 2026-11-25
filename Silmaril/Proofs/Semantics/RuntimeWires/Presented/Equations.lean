module

public import Silmaril.Semantics.RuntimeWires.Presentation.Defs

public section

namespace Silmaril.RuntimeWires.Diagram.Proofs

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {E F : Equations S}

/-- A proof in the original presentation remains valid after adding equations. -/
theorem includeCongruence
    (includeEquation : ∀ {A B} {f g : Diagram S A B}, E f g → F f g)
    {A B} {f g : Diagram S A B} (h : Congruence E f g) : Congruence F f g := by
  induction h with
  | equation h => exact .equation (includeEquation h)
  | refl f => exact .refl f
  | symm _ ih => exact .symm ih
  | trans _ _ ih ih' => exact .trans ih ih'
  | comp _ _ ih ih' => exact .comp ih ih'
  | tensor _ _ ih ih' => exact .tensor ih ih'
  | id_comp f => exact .id_comp f
  | comp_id f => exact .comp_id f
  | comp_assoc f g h => exact .comp_assoc f g h
  | tensor_id A B => exact .tensor_id A B
  | tensor_comp f g h k => exact .tensor_comp f g h k
  | tensor_unit_left f => exact .tensor_unit_left f
  | tensor_unit_right f => exact .tensor_unit_right f
  | tensor_assoc f g h => exact .tensor_assoc f g h

end Silmaril.RuntimeWires.Diagram.Proofs
