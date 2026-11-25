module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonInduction

/-! # Typing coherence for categorical case interpretation

Hidden coproduct summands need not agree between the two derivations. The
common-type comparison induction proves coherence for the unannotated raw
syntax itself, with no added model law.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Categorical case interpretation is independent of every typing witness,
including hidden intermediate sum types and quantitative resource splits. -/
theorem denoteCase_coherent (M : CaseModel.{u,v,w,r} (Ty α) Φ ε)
    {n : Nat} {Γ : QCtx (Ty α) n} {e e' : ε} {t : Term Φ n} {A : Ty α}
    (h : HasType .case Γ e t A) (k : HasType .case Γ e' t A) :
    denoteCase M h = denoteCase M k := by
  classical
  have HI : IterationComparisonRule M.toCaseData (ControlData.case M) := by
    intro n a b _ _ Γ Δ e e' A B h k hc
    cases h with
    | iter cap => exact False.elim cap
  exact TypingComparison.eq M.toCaseData (ControlData.case M) h k
    (hasTypingComparison (F := .case) M.toCaseData (fun cap => False.elim cap) (ControlEnvironment.case M) HI t
      h k (QCtx.Aligned.refl Γ))

end Silmaril.Isotope.Refinement.Models.Denotation
