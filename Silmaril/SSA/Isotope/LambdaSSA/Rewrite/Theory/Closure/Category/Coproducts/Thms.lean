module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Coproducts.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationCoproducts

/-! # Finite coproducts of native λSSA continuation interfaces -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.ContinuationContext

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- There are no source labels to distinguish arrows out of the empty interface. -/
def emptyIsInitial : IsInitial (empty : ContinuationContext Φ Γ) :=
  IsInitial.ofUniqueHom
    (fun Z => (ContinuationFamily.toHom (Y := Z) ⟨labelId, fun i _ hi =>
      (Nat.not_lt_zero i (List.getElem?_eq_some_iff.mp hi).1).elim⟩))
    (fun _ f => Proofs.SSA.Isotope.LambdaSSA.Rewrite.empty_unique f _)

/-- Concatenation with the two label embeddings exhibits a binary coproduct. -/
noncomputable def appendIsColimit (X Y : ContinuationContext Φ Γ) :
    IsColimit (BinaryCofan.mk (X.appendInl Y) (X.appendInr Y)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.appendIsColimit X Y

instance hasInitial : HasInitial (ContinuationContext Φ Γ) :=
  (emptyIsInitial (Φ := Φ) (Γ := Γ)).hasInitial

instance hasBinaryCoproduct (X Y : ContinuationContext Φ Γ) : HasBinaryCoproduct X Y :=
  ⟨⟨⟨_, X.appendIsColimit Y⟩⟩⟩

instance hasBinaryCoproducts : HasBinaryCoproducts (ContinuationContext Φ Γ) :=
  hasBinaryCoproducts_of_hasColimit_pair _

instance hasFiniteCoproducts : HasFiniteCoproducts (ContinuationContext Φ Γ) :=
  hasFiniteCoproducts_of_has_binary_and_initial

end Silmaril.Isotope.LambdaSSA.Region.ContinuationContext
