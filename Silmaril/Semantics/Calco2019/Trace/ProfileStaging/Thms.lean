module

public import Silmaril.Semantics.Calco2019.Trace.ProfileStaging.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.ProfileStaging

/-! # Trace the inner wire of a jointly guarded body -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.TwoStateBody

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D U V : K} (s : TwoStateBody G (P.sum A B) (P.sum C D) U V)

theorem innerTraceBody_guard (hf : G.TraceGuard s.flatTraceBody) :
    G.TraceGuard s.innerTraceBody :=
  Proofs.Feedback.inner_trace_guard s hf

/-- Naturality alone identifies the inner trace with the staged body written
as a substitution of the second state's solution. -/
theorem innerTraceBody_eq_staged (F : G.Fixpoints)
    (hf : G.TraceGuard s.innerTraceBody)
    (hn : F.iterate (s.second ≫ P.map P.assoc (𝟙 V)) (G.map s.second_guard P.assoc (𝟙 V)) =
      F.iterate s.second s.second_guard ≫ P.assoc) :
    F.guardedTrace hf = s.stagedTraceBody F :=
  Proofs.Feedback.inner_trace_eq_staged s F hf hn

/-- Every admissible body with a pair of feedback wires has a two-state presentation. -/
def splitTraceBody {f : P.sum (P.sum A (P.sum U V)) B ⟶ P.sum C (P.sum D (P.sum U V))}
    (hf : G.TraceGuard f) : TwoStateBody G (P.sum A B) (P.sum C D) U V where
  entry := P.inl ≫ traceBody f ≫ P.assocInv
  first := P.inl ≫ P.inr ≫ traceBody f ≫ P.assocInv
  second := P.inr ≫ P.inr ≫ traceBody f ≫ P.assocInv
  guarded := (Proofs.Feedback.split_trace_body hf).guarded

theorem flat_splitTraceBody {f : P.sum (P.sum A (P.sum U V)) B ⟶ P.sum C (P.sum D (P.sum U V))}
    (hf : G.TraceGuard f) : (splitTraceBody hf).flatTraceBody = f :=
  Proofs.Feedback.flat_split_trace_body hf

end Silmaril.Calco2019.Guardedness.TwoStateBody
