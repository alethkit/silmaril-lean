module

public import Silmaril.Semantics.Calco2019.Trace.Equivalence.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Equivalence

/-! # The coproduct feedback and guarded Conway correspondence -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.Feedback

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {trace : G.Feedback}

theorem lawful_ofConway (F : G.Conway) : Lawful F.toFixpoints.feedback where
  toLocalLaws := localLaws_ofConway F
  vanishPair := Proofs.Feedback.pairVanishing_ofConway F

/-- Two-state vanishing and sliding identify duplicate states, giving codiagonal. -/
theorem fixpoints_naturalCodiagonal [HasInitial K] (laws : Lawful trace) :
    (fixpoints laws.toLocalLaws).NaturalCodiagonal :=
  Proofs.Feedback.feedback_codiagonal laws

/-- Recover a guarded Conway operator from lawful coproduct feedback. -/
@[expose]
def conway [HasInitial K] (laws : Lawful trace) : G.Conway where
  toFixpoints := fixpoints laws.toLocalLaws
  naturalCodiagonal := fixpoints_naturalCodiagonal laws
  dinaturality := fixpoints_dinaturality laws.toLocalLaws

/-- Guarded Conway operators and coproduct feedback satisfying tightening,
superposition, shared-result sliding and two-state vanishing correspond bijectively. -/
def conwayEquiv [HasInitial K] : G.Conway ≃ {tr : G.Feedback // Lawful tr} where
  toFun F := ⟨F.toFixpoints.feedback, lawful_ofConway F⟩
  invFun tr := conway tr.property
  left_inv F := by
    cases F with
    | mk fp nc dn =>
      cases fp with
      | mk op fix =>
        simp only [conway, fixpoints, Conway.mk.injEq, Fixpoints.mk.injEq]
        funext X Y f hf
        exact Guardedness.feedback_recovers ⟨op, fix⟩ f hf
  right_inv tr := by
    apply Subtype.ext
    funext A B U f hf
    exact fixpoints_feedback tr.property.toLocalLaws f hf

theorem conway_of_feedback [HasInitial K] (F : G.Conway) :
    conway (lawful_ofConway F) = F :=
  (conwayEquiv (G := G)).left_inv F

end Silmaril.Calco2019.Guardedness.Feedback
