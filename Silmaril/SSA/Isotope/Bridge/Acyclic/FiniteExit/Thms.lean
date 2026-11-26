module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.FiniteExit

/-! # Positional typing and the empty-interface boundary -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Code

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Renaming the outward label leaves the local join binders in place. -/
theorem toSSA_renameLabels {n : Nat} {β : BoundCtx τ n} {A : τ}
    (c : Code Φ β A) (ρ : Nat → Nat) (i : Nat) :
    (c.toSSA i).renameLabels ρ = c.toSSA (ρ i) :=
  toSSA_renameLabels_proof c ρ i

end Silmaril.Isotope.LambdaSSA.Acyclic.Code

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {L : LCtx τ} {n : Nat} {β : BoundCtx τ n}

/-- The actual lowered region has the original ordered label interface. -/
theorem toSSA_hasType (c : FiniteExit Φ L β) :
    Region.HasType β.toList c.toSSA L :=
  toSSA_hasType_proof c

/-- Every admitted finite acyclic region has an outward label. The native
syntax's abort is a term, so it cannot replace a branch at an empty interface. -/
theorem exits_ne_nil (c : FiniteExit Φ L β) : L ≠ [] :=
  exits_ne_nil_proof c

instance : IsEmpty (FiniteExit Φ ([] : LCtx τ) β) :=
  ⟨fun c => c.exits_ne_nil rfl⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit

namespace Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The finite specialization has the same positional region as the binary
comparison, including the decoder block. -/
theorem toSSA_toFinite {A B : τ} {n : Nat} {β : BoundCtx τ n} (c : TwoExit Φ A B β) :
    c.toFinite.toSSA = c.toSSA :=
  toSSA_toFinite_proof c

end Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit
