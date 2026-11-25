module

public import Silmaril.Semantics.Calco2019.Trace.ProfileVanishing.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.ProfileVanishing

/-! # Guarded staged feedback at the marked external interfaces -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.TwoStateBody

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D U V : K} (s : TwoStateBody G (P.sum A B) (P.sum C D) U V)

theorem stagedTraceBody_guard (F : G.Conway) (hf : G.TraceGuard s.flatTraceBody) :
    G.TraceGuard (s.stagedTraceBody F.toFixpoints) :=
  Proofs.Feedback.stagedTraceBody_guard s F hf

/-- Staged vanishing retains the guard on the separately marked output
through both feedback steps. -/
theorem guardedTrace_vanish_pair (F : G.Conway) (hf : G.TraceGuard s.flatTraceBody) :
    F.toFixpoints.guardedTrace hf =
      F.toFixpoints.guardedTrace (s.stagedTraceBody_guard F hf) :=
  Proofs.Feedback.profile_vanish_pair s F hf

end Silmaril.Calco2019.Guardedness.TwoStateBody
