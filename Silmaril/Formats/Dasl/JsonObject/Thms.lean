module

public import Silmaril.Formats.Dasl.JsonObject.Defs
import Silmaril.Proofs.Formats.Dasl.JsonObject

public section

namespace Silmaril.Formats.Dasl.JsonObject

open Semantics.Naming

@[simp] theorem decode_encode (object : Object) : decode? (encode object) = some object :=
  Proofs.Formats.Dasl.JsonObject.decode_encode object

theorem encode_injective : Function.Injective encode :=
  fun _ _ same => Option.some.inj (by simpa only [decode_encode] using congrArg decode? same)

theorem encoded_eq_iff {left right : Object} : encode left = encode right ↔ left = right :=
  ⟨fun same => encode_injective same, congrArg encode⟩

/-- A total, coherent *fixed* profile gives exactly one name per supported object.
The theorem asserts neither that all profiles agree nor that different objects cannot collide. -/
theorem exactly_one_name (profile : Profile) (object : Object) :
    ∃! name, names profile name object := by
  obtain ⟨name, found⟩ := profile.total (encode object)
  exact ⟨name, found, fun _ other => profile.coherent other found⟩

/-- Distinct objects cannot share a name if the observed byte relation is also binding. -/
theorem names_binding (profile : Profile) (bound : Binding profile.observe) : Binding (names profile) :=
  fun _ _ _ first second => encode_injective (bound first second)

end Silmaril.Formats.Dasl.JsonObject
