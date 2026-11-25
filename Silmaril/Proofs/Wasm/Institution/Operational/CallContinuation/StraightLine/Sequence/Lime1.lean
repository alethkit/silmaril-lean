module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Rules
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Value)
open OuterCall.Computed

private theorem attach_code {site : Site} (i : site.TargetId) (rest : List (Op site)) (q : CallFrame.State) :
    limeCode site (attach i rest q) =
      CallFrame.limeCode (site.target i).address (site.target i).callee q ++ rest.map (emit limeSyntax) := by
  cases q with
  | trapped => simp only [attach, limeCode, render, CallFrame.limeCode, CallFrame.legacyCode, values, List.append_assoc, List.singleton_append]
  | _ => rfl

private theorem resolve_iff {H : Type} {s : Store H} {site : Site} {i : site.TargetId}
    {saved args : List Value} {rest : List (Op site)} {dst : Config H} (g : LimeGuard s site) :
    Step CallFrame.limeNoHost (limeConfig s site (.running (saved ++ args) (.call i :: rest))) dst ↔
      dst = limeConfig s site (.active i (.invoke saved args) rest) := by
  have exactly := lime_direct_call_iff (s := s) (f := site.frame) (dst := dst)
    (stack := saved ++ args) (tail := rest.map (emit limeSyntax)) (g.resolves i)
  simp only [limeConfig, limeCode, render, CallFrame.limeCode, CallFrame.legacyCode, values, List.append_assoc, List.singleton_append]
  exact exactly

theorem sound {H : Type} {s : Store H} {site : Site} {a b : State site}
    (g : LimeGuard s site) (edge : Edge site a b) :
    Step CallFrame.limeNoHost (limeConfig s site a) (limeConfig s site b) := by
  cases invert edge with
  | @call i before after rest _ move =>
    have native := CallFrame.lime_sound (caller := site.frame) (g.allocated i) move
    simp only [limeConfig, attach_code]
    have lifted : Step CallFrame.limeNoHost
        ⟨s, site.frame, CallFrame.limeCode (site.target i).address (site.target i).callee before ++ rest.map (emit limeSyntax)⟩
        ⟨s, site.frame, CallFrame.limeCode (site.target i).address (site.target i).callee after ++ rest.map (emit limeSyntax)⟩ := by
      simpa only [values, List.map_nil, List.nil_append] using Step.context native [] (rest.map (emit limeSyntax))
    exact lifted
  | ground rule =>
    cases rule with
    | resolve => exact (resolve_iff g).mpr rfl
    | discard cut => exact (Prefix.lime_discard_iff (f := site.frame) (emit (site := site) limeSyntax)).mpr ⟨_, _, cut, rfl⟩
    | @numeric stack op rest out move =>
      have native := Prefix.lime_step_iff (s := s) (f := site.frame)
        (tail := rest.map (emit limeSyntax)) |>.mpr ⟨out, move, rfl⟩
      cases out <;> exact native

theorem readback {H : Type} {s : Store H} {site : Site} {a : State site}
    {dst : Config H} (g : LimeGuard s site) (ready : Admitted site a) (h : Step CallFrame.limeNoHost (limeConfig s site a) dst) :
    ∃ out, Edge site a out ∧ dst = limeConfig s site out := by
  cases a with
  | active i phase rest =>
    obtain ⟨mid, step, eq⟩ := CallContinuation.lime_active_strip (caller := site.frame) ready.1 h
    obtain ⟨out, move, rfl⟩ := (CallFrame.lime_step_iff (g.allocated i) ready.2.1).mp step
    exact ⟨attach i rest out, call ready.1 move, eq.trans (by rw [limeConfig, attach_code]; rfl)⟩
  | trapped stack rest =>
    obtain ⟨kept, remaining, cut, eq⟩ :=
      (Prefix.lime_discard_iff (f := site.frame) (emit (site := site) limeSyntax)).mp h
    exact ⟨.trapped kept remaining, fact (.discard cut), eq⟩
  | running stack rest =>
    cases rest with
    | nil =>
      obtain ⟨op, mem, bad⟩ := h.nonvalue
      have member : op ∈ values stack := by
        simpa only [limeConfig, limeCode, render, List.map_nil, List.append_nil] using mem
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp member
      simp at bad
    | cons op rest =>
      cases op with
      | numeric op =>
        obtain ⟨out, move, eq⟩ := (Prefix.lime_step_iff (f := site.frame) (op := op)
          (tail := rest.map (emit limeSyntax))).mp h
        exact ⟨afterOp rest out, fact (.numeric move), eq.trans (by cases out <;> rfl)⟩
      | call i =>
        obtain ⟨saved, args, rfl, count⟩ := split ready
        exact ⟨_, fact (.resolve i saved args rest count), (resolve_iff g).mp h⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs.Lime1
