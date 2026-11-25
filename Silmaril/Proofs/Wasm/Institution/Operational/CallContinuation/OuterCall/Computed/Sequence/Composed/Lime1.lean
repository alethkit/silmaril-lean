module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value)
open Computed.Proofs.Lime1 (lift_body read_body label_stays call_iff)
open Sequence.Proofs.Lime1 (op_stays)

private theorem evaluating_code (site : Site) (stack : List Value) (remaining : List Prefix.Op) :
    limeCode site (evaluating stack remaining) =
      [.frame site.innerSite.arity site.toSite.frame [.label site.innerSite.arity []
        (values stack ++ (site.pending remaining).map (site.emit limeSyntax))]] := by
  cases remaining with
  | cons => rfl
  | nil =>
    simp only [evaluating, limeCode, render, StraightLine.limeCode, StraightLine.render, StraightLine.limeBody,
      StraightLine.renderBody, Site.innerSite, List.nil_append, Site.pending, List.map_nil, List.map_cons,
      List.map_map, Function.comp_def, Site.emit]

private theorem after_code (site : Site) (rest : List Prefix.Op) (out : Prefix.Outcome) :
    limeCode site (afterArg site rest out) =
      [.frame site.innerSite.arity site.toSite.frame [.label site.innerSite.arity []
        (Prefix.outcomeCode values .trap ((site.pending rest).map (site.emit limeSyntax)) out)]] := by
  cases out with
  | values => exact evaluating_code _ _ _
  | trap => rfl

private theorem trap_code (site : Site) (stack : List Value) (rest : List Pending) :
    limeCode site (argumentTrap stack rest) = limeCode site (.argumentTrap stack rest) := by
  cases stack <;> cases rest <;> rfl

private theorem body_expression (site : Site) :
    expression site.limeFunc.body = site.body limeSyntax := by
  change (site.body limeSource).map Execution.Runtime.AdminInstr.source = _
  simp only [Site.body, List.map_map]
  apply List.map_congr_left
  intro ins _
  cases ins with
  | op op => cases op <;> rfl
  | call => rfl

private theorem enter_iff {H : Type} {s : Store H} {caller : Frame}
    {site : Site} {dst : Config H} (g : LimeGuard s caller site) :
    Step CallFrame.limeNoHost (limeConfig s caller site .invoke) dst ↔
      dst = limeConfig s caller site (evaluating [] site.prefixCode) := by
  have count : site.args.length = site.type.params.length := by
    simpa [Site.type] using congrArg List.length g.typed.outerArgs
  have enter := CallFrame.lime_invoke_wasm_exact (caller := caller) (dst := dst) g.outerAlloc count
  rw [body_expression] at enter
  simp only [limeConfig, evaluating_code]
  exact enter

private theorem eval_iff {H : Type} {s : Store H} {caller : Frame}
    {site : Site} {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op} {dst : Config H} :
    Step CallFrame.limeNoHost (limeConfig s caller site (.args stack (op :: rest))) dst ↔
      ∃ out, Prefix.Reduce site.toSite.frame.locals stack op out ∧ dst = limeConfig s caller site (afterArg site rest out) := by
  constructor
  · intro step
    obtain ⟨mid, h, eq⟩ := read_body
      (op_stays (stack := stack) (op := op) (tail := (site.pending rest).map (site.emit limeSyntax))) step
    obtain ⟨out, reduce, rfl⟩ := Prefix.lime_step_iff.mp h
    exact ⟨out, reduce, eq.trans (by rw [limeConfig, after_code])⟩
  · rintro ⟨out, reduce, rfl⟩
    have move := Prefix.lime_step_iff (s := s) (f := site.toSite.frame)
      (tail := (site.pending rest).map (site.emit limeSyntax)) |>.mpr ⟨out, reduce, rfl⟩
    simp only [limeConfig, after_code]
    exact lift_body move

theorem sound {H : Type} {s : Store H} {caller : Frame}
    {site : Site} {a b : State} (g : LimeGuard s caller site) (edge : Edge site a b) :
    Step CallFrame.limeNoHost (limeConfig s caller site a) (limeConfig s caller site b) := by
  cases invert edge with
  | callInner move => exact StraightLine.lime_sound g.innerGuard move
  | ground rule =>
    cases rule with
    | resolve => exact (call_iff g.outerLookup).mpr rfl
    | enter => exact (enter_iff g).mpr rfl
    | evaluate h => exact eval_iff.mpr ⟨_, h, rfl⟩
    | discard cut =>
      have move := Prefix.lime_discard_iff (s := s) (f := site.toSite.frame)
        (site.emit limeSyntax) |>.mpr ⟨_, _, cut, rfl⟩
      simp only [limeConfig, trap_code]
      exact lift_body (caller := caller) (n := site.innerSite.arity) move

theorem readback {H : Type} {s : Store H} {caller : Frame}
    {site : Site} {a : State} {dst : Config H} (g : LimeGuard s caller site) (ready : Admitted site a)
    (h : Step CallFrame.limeNoHost (limeConfig s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = limeConfig s caller site out := by
  cases a with
  | call => exact ⟨.invoke, fact .resolve, (call_iff g.outerLookup).mp h⟩
  | invoke => exact ⟨_, fact .enter, (enter_iff g).mp h⟩
  | inner phase =>
    obtain ⟨out, move, eq⟩ := (StraightLine.lime_step_iff g.innerGuard ready).mp h
    exact ⟨.inner out, delegate move, eq⟩
  | args stack rest =>
    cases rest with
    | nil => exact (ready.1 rfl).elim
    | cons op rest =>
      obtain ⟨out, move, eq⟩ := eval_iff.mp h
      exact ⟨_, fact (.evaluate move), eq⟩
  | argumentTrap stack rest =>
    have nonempty : stack ≠ [] ∨ rest.map (site.emit limeSyntax) ≠ [] := by
      simpa [Admitted] using ready
    obtain ⟨mid, move, eq⟩ := read_body (label_stays (head := .trap) (stack := stack) rfl (by simp) (by simp) (fun _ => nonempty)) h
    obtain ⟨kept, rest, cut, rfl⟩ := (Prefix.lime_discard_iff (f := site.toSite.frame) (site.emit limeSyntax)).mp move
    refine ⟨argumentTrap kept rest, fact (.discard cut), ?_⟩
    simp only [limeConfig, trap_code]
    exact eq

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Proofs.Lime1
