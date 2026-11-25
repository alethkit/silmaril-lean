module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Defs

/-! # The sum of two types in the paper singleton category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Include each type as a singleton exit interface with empty capture. -/
abbrev toInterface (Φ : Type v) [HasTy Φ τ] :
    TypeCategory (τ := τ) Φ ⥤ Interface Φ ([] : VCtx τ) :=
  inducedFunctor (fun A : τ => (⟨[A]⟩ : Interface Φ ([] : VCtx τ)))

/-- The sum-typed singleton with its two tagged injections. -/
@[expose] def sumCofan (A B : τ) : BinaryCofan (ofType (Φ := Φ) A) (ofType B) :=
  BinaryCofan.mk
    (InducedCategory.homMk (Y := ofType (Silmaril.coprod A B))
      (singletonSumCofan (Φ := Φ) (Γ := []) A B).inl)
    (InducedCategory.homMk (singletonSumCofan (Φ := Φ) (Γ := []) A B).inr)

/-- The empty decoder guards its impossible input by a local self-loop. -/
theorem emptyRegion_typed (A : τ) :
    ValueBranches [Silmaril.empty] (unpackExits ([] : LCtx τ) : Region Φ) [A] :=
  .cfg (fun _ : Fin 1 => Silmaril.empty) (.br (ℓ := 0) rfl (.var (i := 0) rfl))
    (fun _ => .br (ℓ := 0) rfl (.var (i := 0) rfl))

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
