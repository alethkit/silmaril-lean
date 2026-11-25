module

public import Silmaril.Semantics.Calco2019.Trace.ProfileEquivalence.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.ProfileEquivalence

/-! # The four-interface trace and guarded Conway correspondence -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.FourInterfaceTrace

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

theorem lawful_ofConway (F : G.Conway) : (ofConway F).Lawful where
  toLocalLaws := localLaws_ofConway F
  vanishPair s hf := Proofs.Feedback.vanish_pair_ofConway F s hf

theorem toFeedback_lawful [HasInitial K] {I : K} (i : IsInitial I)
    (T : G.FourInterfaceTrace) (laws : T.Lawful) :
    Feedback.Lawful (T.toFeedback i) where
  toLocalLaws := T.toFeedback_localLaws i laws.toLocalLaws
  vanishPair := Proofs.Feedback.reduced_vanish_pair i T laws

/-- Vanishing II applies to any admissible body with a pair of feedback wires. -/
theorem vanishPair_body (T : G.FourInterfaceTrace) (laws : T.Lawful)
    {A B C D U V : K} {f : P.sum (P.sum A (P.sum U V)) B ⟶ P.sum C (P.sum D (P.sum U V))}
    (hf : G.TraceGuard f) :
    let s := TwoStateBody.splitTraceBody hf
    let h := (TwoStateBody.flat_splitTraceBody hf).symm ▸ hf
    T.run hf = T.run (T.guarded (s.innerTraceBody_guard h)) := by
  let h := (TwoStateBody.flat_splitTraceBody hf).symm ▸ hf
  exact (Proofs.Feedback.profile_run_eq T (TwoStateBody.flat_splitTraceBody hf).symm hf h).trans
    (laws.vanishPair _ h)

/-- Recover a Conway operator from the full four-interface trace laws. -/
@[expose]
noncomputable def conway [HasInitial K] (T : G.FourInterfaceTrace) (laws : T.Lawful) : G.Conway :=
  Feedback.conway (T.toFeedback_lawful initialIsInitial laws)

theorem ofConway_run [HasInitial K] (T : G.FourInterfaceTrace) (laws : T.Lawful)
    {A B C D U : K} {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)} (hf : G.TraceGuard f) :
    (ofConway (T.conway laws)).run hf = T.run hf :=
  (Feedback.fixpoints_feedback (T.toFeedback_lawful initialIsInitial laws).toLocalLaws
    _ (traceBody_guard hf)).trans (T.toFeedback_run initialIsInitial laws.tighten hf)

/-- The mutually inverse correspondence of Goncharov–Schröder,
Proposition 32, cited by CALCO 2019 Article 13, Remark 15. -/
noncomputable def conwayEquiv [HasInitial K] : G.Conway ≃ {T : G.FourInterfaceTrace // T.Lawful} where
  toFun F := ⟨ofConway F, lawful_ofConway F⟩
  invFun T := T.val.conway T.property
  left_inv F := Proofs.Feedback.conway_of_profile_feedback initialIsInitial F _
  right_inv T := Subtype.ext (Proofs.Feedback.profile_ext (fun hf => ofConway_run T.val T.property hf))

end Silmaril.Calco2019.Guardedness.FourInterfaceTrace
