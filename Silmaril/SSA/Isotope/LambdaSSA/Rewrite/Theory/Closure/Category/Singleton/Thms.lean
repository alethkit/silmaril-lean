module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationSingleton

/-! # Coproduct type formers in the native λSSA continuation category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.ContinuationContext

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The two injections route their payload to the single sum-typed label. -/
def sumTag (A B : τ) :
    (single A : ContinuationContext Φ Γ).append (single B) ⟶ single (Silmaril.coprod A B) :=
  ContinuationFamily.toHom ⟨sumTagRegion, Proofs.SSA.Isotope.LambdaSSA.Rewrite.sumTag_valueFamily A B⟩

/-- The left singleton injection is represented by a branch of the tagged payload. -/
theorem appendInl_sumTag (A B : τ) :
    (single A : ContinuationContext Φ Γ).appendInl (single B) ≫ sumTag A B =
      singletonToHom (A := A) (Y := single (Silmaril.coprod A B))
        (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl))) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.appendInl_sumTag A B

/-- The right singleton injection is represented by a branch of the tagged payload. -/
theorem appendInr_sumTag (A B : τ) :
    (single A : ContinuationContext Φ Γ).appendInr (single B) ≫ sumTag A B =
      singletonToHom (A := B) (Y := single (Silmaril.coprod A B))
        (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl))) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.appendInr_sumTag A B

/-- The tagged sum is isomorphic to the pair of single-label interfaces. -/
def singletonSumIso (A B : τ) :
    (single A : ContinuationContext Φ Γ).append (single B) ≅ single (Silmaril.coprod A B) where
  hom := sumTag A B
  inv := sumCase A B
  hom_inv_id := Proofs.SSA.Isotope.LambdaSSA.Rewrite.sumTag_sumCase A B
  inv_hom_id := Proofs.SSA.Isotope.LambdaSSA.Rewrite.sumCase_sumTag A B

/-- The sum type is a coproduct of the singleton interfaces for its summands. -/
noncomputable def singletonSumIsColimit (A B : τ) :
    IsColimit (BinaryCofan.mk
      (((single A : ContinuationContext Φ Γ).appendInl (single B)) ≫ sumTag A B)
      (((single A : ContinuationContext Φ Γ).appendInr (single B)) ≫ sumTag A B)) :=
  IsColimit.ofIsoColimit ((single A).appendIsColimit (single B))
    (Cocone.ext (singletonSumIso A B) (by rintro ⟨_ | _⟩ <;> rfl))

/-- The syntactic empty type represents an initial interface. -/
noncomputable def singletonEmptyIsInitial :
    IsInitial (single (Silmaril.empty : τ) : ContinuationContext Φ Γ) :=
  emptyIsInitial.ofIso (Classical.choice ((empty : ContinuationContext Φ Γ).nonempty_packedIso))

end Silmaril.Isotope.LambdaSSA.Region.ContinuationContext
