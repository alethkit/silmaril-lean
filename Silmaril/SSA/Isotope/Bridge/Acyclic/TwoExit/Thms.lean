module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TwoExit

/-! # The exact two-exit typing square -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ}

/-- The decoder sends each arm's payload to the corresponding label. -/
theorem decoder_hasType (Γ : VCtx τ) :
    Region.HasType (coprod A B :: Γ) (decoder : Region Φ) [A, B] :=
  .case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.var rfl))

/-- Lowering exposes the two labels to the existing positional typing API. -/
theorem toSSA_hasType {n : Nat} {β : BoundCtx τ n} (c : TwoExit Φ A B β) :
    Region.HasType β.toList c.toSSA [A, B] :=
  toSSA_hasType_proof c

@[simp] theorem encode_decode {n : Nat} {β : BoundCtx τ n} (c : Code Φ β (coprod A B)) :
    (decode c).encode = c :=
  rfl

/-- Compilation of a decoded LetCase operand recovers the original term
and its exact typing derivation. -/
theorem encode_decodeLetCase {n : Nat} {β : BoundCtx τ n}
    (a : Operand Φ β (coprod A B)) : (decodeLetCase a).encode.toLetCase = a :=
  Code.toLetCase_ofLetCase a.2

end Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit
