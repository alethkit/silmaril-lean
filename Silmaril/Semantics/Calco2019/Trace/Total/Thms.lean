module

public import Silmaril.Semantics.Calco2019.Trace.Total.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Total

/-! # Ordinary trace is equivalent to Conway iteration under the total guard -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.Feedback

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K}
  {tr : Guardedness.Feedback (Guardedness.greatest P)}

theorem JoyalStreetVerity.localLaws (laws : JoyalStreetVerity tr) : LocalLaws tr where
  tighten := laws.tighten
  superpose := laws.superpose
  slide f h _ := Proofs.Feedback.total_slide_shared laws f h

theorem JoyalStreetVerity.lawful [HasInitial K] (laws : JoyalStreetVerity tr) : Lawful tr where
  toLocalLaws := laws.localLaws
  vanishPair := (Proofs.Feedback.total_pair_iff laws.localLaws).2 laws.vanishPair

theorem joyalStreetVerity_ofConway [HasInitial K] (F : (Guardedness.greatest P).Conway) :
    JoyalStreetVerity F.toFixpoints.feedback :=
  Proofs.Feedback.total_ofConway F

/-- The ordinary co-Cartesian trace correspondence cited in Remark 15. -/
def totalConwayEquiv [HasInitial K] :
    (Guardedness.greatest P).Conway ≃
      {tr : Guardedness.Feedback (Guardedness.greatest P) // JoyalStreetVerity tr} :=
  (conwayEquiv (G := Guardedness.greatest P)).trans
    { toFun := fun t => ⟨t.val, Proofs.Feedback.total_of_lawful t.property⟩
      invFun := fun t => ⟨t.val, t.property.lawful⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

/-- Vanishing II applies to any body with a coproduct as feedback object. -/
theorem JoyalStreetVerity.vanishPair_body (laws : JoyalStreetVerity tr) {A B U V : K}
    (f : P.sum A (P.sum U V) ⟶ P.sum B (P.sum U V)) :
    let s := splitTotalBody f
    tr f True.intro =
      tr (onBranches (G := Guardedness.greatest P) tr
        (P.desc s.entry s.first) s.second True.intro) True.intro :=
  Proofs.Feedback.total_pair_body laws f

end Silmaril.Calco2019.Guardedness.Feedback
