module

public import Silmaril.Semantics.Calco2019.Trace.Converse.Defs
public import Silmaril.Semantics.Calco2019.Trace.Vanishing.Thms
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse

/-! # Recovering a fixpoint from coproduct feedback -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.Feedback

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {trace : G.Feedback} (laws : LocalLaws trace)

include laws
/-- The entry feeds into the copairing of an immediate return and the recovered dagger. -/
theorem onBranches_formula [HasInitial K] {A B U : K}
    (entry : A ⟶ P.sum B U) (body : U ⟶ P.sum B U) (hb : G.guarded body) :
    onBranches trace entry body hb = entry ≫ P.desc (𝟙 B) (iterate trace body hb) :=
  Proofs.Feedback.onBranches_formula laws entry body hb

/-- Feedback satisfying the local laws induces a guarded fixpoint operator. -/
@[expose]
def fixpoints [HasInitial K] : G.Fixpoints where
  iterate := fun f hf => iterate trace f hf
  fixpoint f hf := by exact Proofs.Feedback.feedback_fixpoint laws f hf

/-- The recovered iteration is natural in the return object. -/
theorem iterate_natural {U B B' : K} (f : U ⟶ P.sum B U) (b : B ⟶ B') (hf : G.guarded f)
    (hg : G.guarded (f ≫ P.map b (𝟙 U))) :
    iterate trace (f ≫ P.map b (𝟙 U)) hg = iterate trace f hf ≫ b :=
  Proofs.Feedback.feedback_naturality laws f b hf hg

/-- The recovered fixpoints satisfy dinaturality with either of the recursive branches guarded. -/
theorem fixpoints_dinaturality [HasInitial K] : (fixpoints laws).Dinaturality := by
  intro U V B g h guard hg hh
  exact Proofs.Feedback.feedback_dinaturality laws g h guard

/-- Forming feedback from the recovered fixpoints returns the original operation. -/
theorem fixpoints_feedback [HasInitial K] {A B U : K}
    (f : P.sum A U ⟶ P.sum B U) (hf : G.FeedbackGuard f) :
    (fixpoints laws).feedback f hf = trace f hf := by
  have e : P.desc (P.inl ≫ f) (P.inr ≫ f) = f := by
    apply P.hom_ext <;> simp
  change P.inl ≫ f ≫ P.desc (𝟙 B) (iterate trace (P.inr ≫ f) hf) = trace f hf
  exact (Category.assoc _ _ _).symm.trans
    ((onBranches_formula laws (P.inl ≫ f) (P.inr ≫ f) hf).symm.trans
      (Proofs.Feedback.trace_eq e _ _))

end Silmaril.Calco2019.Guardedness.Feedback
