module

public import Silmaril.Semantics.Calco2019.Trace.ProfileEquivalence.Thms
public import Silmaril.Semantics.Calco2019.Trace.Total.Thms
import Silmaril.Proofs.Semantics.Calco2019.Trace.Compatibility

/-! # Compatibility of guarded and ordinary trace conversions -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.FourInterfaceTrace

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- The feedback reconstructed through the converse is the direct
restriction to initial marked ports. -/
theorem conway_feedback [HasInitial K] {I : K} (i : IsInitial I)
    (T : G.FourInterfaceTrace) (laws : T.Lawful) :
    @Eq G.Feedback (T.conway laws).toFixpoints.feedback (T.toFeedback i) :=
  Proofs.TraceCompatibility.conway_feedback i T laws

/-- When every body is guarded, the four-interface laws and the ordinary
Joyal–Street–Verity laws give equivalent trace operations. -/
noncomputable def totalTraceEquiv [HasInitial K] :
    {T : (greatest P).FourInterfaceTrace // T.Lawful} ≃
      {tr : (greatest P).Feedback // Feedback.JoyalStreetVerity tr} :=
  (conwayEquiv (G := greatest P)).symm.trans Feedback.totalConwayEquiv

/-- The equivalence specializes to the direct restriction, with no
dependence on the choice of the initial object. -/
theorem totalTraceEquiv_feedback [HasInitial K] {I : K} (i : IsInitial I)
    (T : {T : (greatest P).FourInterfaceTrace // T.Lawful}) :
    @Eq (greatest P).Feedback (totalTraceEquiv T).val (T.val.toFeedback i) := by
  unfold totalTraceEquiv
  refine (Feedback.totalConwayEquiv_feedback (conwayEquiv.symm T)).trans ?_
  rw [conwayEquiv_symm_conway]
  exact conway_feedback i T.val T.property

end Silmaril.Calco2019.Guardedness.FourInterfaceTrace
