module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Thms

/-! # Native continuation composition after binding branch arguments -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L K P : LCtx τ}

/-- Bind the producer's branch arguments before substituting the consumer.
The consumer needs only exact typing. -/
@[expose] def TypedContinuationFamily.compAfterBinding
    (σ : TypedContinuationFamily (Φ := Φ) Γ L K) (υ : TypedContinuationFamily (Φ := Φ) Γ K P) :
    TypedContinuationFamily (Φ := Φ) Γ L P :=
  let σ' := (ContinuationFamily.ofTyped σ.property).toTyped
  ⟨compLSubst σ'.val υ.val, σ'.property.comp υ.property⟩

/-- Composition after binding descends to pointwise native rewrite classes. -/
@[expose] def TypedContinuationClass.compAfterBinding
    (f : TypedContinuationClass (Φ := Φ) Γ L K) (g : TypedContinuationClass (Φ := Φ) Γ K P) :
    TypedContinuationClass (Φ := Φ) Γ L P :=
  Quotient.map₂ TypedContinuationFamily.compAfterBinding
    (fun σ _ hσ _ _ hυ => LSubst.comp_substitutionEquiv
      (fun _ _ hi => (hσ hi).bindBranchArguments) hυ (ContinuationFamily.ofTyped σ.property).property) f g

end Silmaril.Isotope.LambdaSSA.Region
