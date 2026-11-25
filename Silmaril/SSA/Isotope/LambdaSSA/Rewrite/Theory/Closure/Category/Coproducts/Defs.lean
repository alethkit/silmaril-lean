module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Thms
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! # Chosen coproduct interfaces for native λSSA continuations -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.ContinuationContext

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The interface with no source exits. -/
@[expose] def empty : ContinuationContext Φ Γ := ⟨[]⟩

/-- The interface consisting of the left exits followed by the right exits. -/
@[expose] def append (X Y : ContinuationContext Φ Γ) : ContinuationContext Φ Γ :=
  ⟨X.labels ++ Y.labels⟩

/-- The left injection keeps the original label indices and arguments. -/
@[expose] def appendInl (X Y : ContinuationContext Φ Γ) : X ⟶ X.append Y :=
  ContinuationFamily.toHom ⟨labelId, fun _ _ hi =>
    .br ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1).trans hi) (.var rfl)⟩

/-- The right injection shifts each label index by the size of the left interface. -/
@[expose] def appendInr (X Y : ContinuationContext Φ Γ) : Y ⟶ X.append Y :=
  ContinuationFamily.toHom ⟨fun i => labelId (X.labels.length + i), fun i _ hi => by
    exact .br (by simpa only [At, append, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left] using hi) (.var rfl)⟩

end Silmaril.Isotope.LambdaSSA.Region.ContinuationContext
