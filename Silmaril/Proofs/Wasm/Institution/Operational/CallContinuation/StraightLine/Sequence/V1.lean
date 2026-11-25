module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Transport
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs.V1

open Wasm.V1.Execution
open OuterCall.Computed

private theorem attach_code {site : Site} (i : site.TargetId) (rest : List (Op site)) (q : CallFrame.State) :
    v1Code site (attach i rest q) =
      CallFrame.v1Code (site.target i).address (site.target i).callee q ++ rest.map (emit v1Syntax) := by
  cases q with
  | trapped =>
    simp only [attach, v1Code, render, CallFrame.v1Code, CallFrame.legacyCode, values, List.append_assoc,
      List.singleton_append]
  | _ => rfl

theorem sound {H : Type} {s : Store H} {site : Site} {a b : State site}
    (g : V1Guard s site) (edge : Edge site a b) :
    Step CallFrame.v1NoHost (v1Config s site a) (v1Config s site b) := by
  cases invert edge with
  | @call i before after rest _ move =>
    have native := CallFrame.v1_sound (caller := site.frame) (g.allocated i) move
    simp only [v1Config, attach_code]
    have lifted : Step CallFrame.v1NoHost
        ⟨s, site.frame, CallFrame.v1Code (site.target i).address (site.target i).callee before ++ rest.map (emit v1Syntax)⟩
        ⟨s, site.frame, CallFrame.v1Code (site.target i).address (site.target i).callee after ++ rest.map (emit v1Syntax)⟩ := by
      simpa only [values, List.map_nil, List.nil_append] using Step.context native [] (rest.map (emit v1Syntax))
    exact lifted
  | ground rule =>
    cases rule with
    | resolve i saved args rest _ =>
      have native := Step.context (Step.call (host := CallFrame.v1NoHost) s site.frame _ _ (g.resolves i))
        (saved ++ args) (rest.map (emit v1Syntax))
      change Step CallFrame.v1NoHost
        ⟨s, site.frame, values (saved ++ args) ++ .source (.call (site.target i).index) :: rest.map (emit v1Syntax)⟩
        ⟨s, site.frame, values (saved ++ args) ++ [.invoke (site.target i).address] ++ rest.map (emit v1Syntax)⟩
      simpa only [List.append_assoc, List.singleton_append] using native
    | discard cut =>
      exact (Prefix.v1_discard_iff (f := site.frame) (emit (site := site) v1Syntax)).mpr ⟨_, _, cut, rfl⟩
    | @numeric stack op rest out move =>
      have native := Prefix.v1_step_iff (s := s) (f := site.frame)
        (tail := rest.map (emit v1Syntax)) |>.mpr ⟨out, move, rfl⟩
      cases out <;> exact native

theorem readback {H : Type} {s : Store H} {site : Site} {a : State site} {dst : Config H}
    (g : V1Guard s site) (ready : Admitted site a) (h : Step CallFrame.v1NoHost (v1Config s site a) dst) :
    ∃ out, Edge site a out ∧ dst = v1Config s site out := by
  have mapped := h.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ proof => proof)
  rw [v1_to_lime] at mapped
  obtain ⟨out, edge, eq⟩ := Lime1.readback (guard_to_lime g) ready mapped
  exact ⟨out, edge, CallContinuation.config_toLime_injective H (eq.trans (v1_to_lime s site out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs.V1
