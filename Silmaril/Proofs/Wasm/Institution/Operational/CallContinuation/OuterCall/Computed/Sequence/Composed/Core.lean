module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Proofs.Core

open Execution.Core
open Execution.Runtime (Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)
open Computed.Proofs.Core (lift_body read_body label_stays call_iff)
open Sequence.Proofs.Core (op_stays wasm_entry_iff frame_init)

private theorem evaluating_code (site : Site) (stack : List Value) (remaining : List Prefix.Op) :
    coreCode site (evaluating stack remaining) =
      [.frame site.innerSite.arity site.toSite.frame.toCore [.label site.innerSite.arity []
        (coreValues stack ++ (site.pending remaining).map (site.emit coreSyntax))]] := by
  cases remaining with
  | cons => rfl
  | nil =>
    simp only [evaluating, coreCode, render, StraightLine.coreCode, StraightLine.render, StraightLine.coreBody,
      StraightLine.renderBody, Site.innerSite, List.nil_append, Site.pending, List.map_nil, List.map_cons,
      List.map_map, Function.comp_def, Site.emit]

private theorem after_code (site : Site) (rest : List Prefix.Op) (out : Prefix.Outcome) :
    coreCode site (afterArg site rest out) =
      [.frame site.innerSite.arity site.toSite.frame.toCore [.label site.innerSite.arity []
        (Prefix.outcomeCode coreValues .trap ((site.pending rest).map (site.emit coreSyntax)) out)]] := by
  cases out with
  | values => exact evaluating_code _ _ _
  | trap => rfl

private theorem trap_code (site : Site) (stack : List Value) (rest : List Pending) :
    coreCode site (argumentTrap stack rest) = coreCode site (.argumentTrap stack rest) := by
  cases stack <;> cases rest <;> rfl

private theorem body_expression (site : Site) :
    expression site.coreFunc.body = site.body coreSyntax := by
  change (site.body coreSource).map Admin.plain = _
  simp only [Site.body, List.map_map]
  apply List.map_congr_left
  intro ins _
  cases ins with
  | op op => cases op <;> rfl
  | call => rfl

private theorem enter_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {dst : Config H} (g : CoreGuard s caller site) :
    Step P noHost (coreConfig s caller site .invoke) dst ↔
      dst = coreConfig s caller site (evaluating [] site.prefixCode) := by
  have enter := wasm_entry_iff (P := P) (caller := caller) (dst := dst) g.outerAlloc g.typed.outerArgs
  have init := frame_init site.toSite
  change Frame.forCall site.outerModule.toCore (site.args.map Value.toCore) site.coreFunc.locals = _ at init
  rw [init, body_expression] at enter
  simp only [coreConfig, evaluating_code]
  exact enter

private theorem eval_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op} {dst : Config H} :
    Step P noHost (coreConfig s caller site (.args stack (op :: rest))) dst ↔
      ∃ out, Prefix.Reduce site.toSite.frame.locals stack op out ∧ dst = coreConfig s caller site (afterArg site rest out) := by
  constructor
  · intro step
    obtain ⟨mid, h, eq⟩ := read_body
      (op_stays (stack := stack) (op := op) (tail := (site.pending rest).map (site.emit coreSyntax))) step
    obtain ⟨out, reduce, rfl⟩ := Prefix.core_step_iff.mp h
    exact ⟨out, reduce, eq.trans (by rw [coreConfig, after_code])⟩
  · rintro ⟨out, reduce, rfl⟩
    have move := Prefix.core_step_iff (s := s) (P := P) (f := site.toSite.frame)
      (tail := (site.pending rest).map (site.emit coreSyntax)) |>.mpr ⟨out, reduce, rfl⟩
    simp only [coreConfig, after_code]
    exact lift_body move

theorem sound {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {a b : State} (g : CoreGuard s caller site) (edge : Edge site a b) :
    Step P noHost (coreConfig s caller site a) (coreConfig s caller site b) := by
  cases invert edge with
  | callInner move => exact StraightLine.core_sound g.innerGuard move
  | ground rule =>
    cases rule with
    | resolve => exact (call_iff g.outerLookup g.outerAlloc).mpr rfl
    | enter => exact (enter_iff g).mpr rfl
    | evaluate h => exact eval_iff.mpr ⟨_, h, rfl⟩
    | discard cut =>
      have move := Prefix.core_discard_iff (s := s) (P := P) (f := site.toSite.frame)
        (site.emit coreSyntax) |>.mpr ⟨_, _, cut, rfl⟩
      simp only [coreConfig, trap_code]
      exact lift_body (caller := caller.toCore) (n := site.innerSite.arity) move

theorem readback {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {a : State} {dst : Config H} (g : CoreGuard s caller site) (ready : Admitted site a)
    (h : Step P noHost (coreConfig s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = coreConfig s caller site out := by
  cases a with
  | call => exact ⟨.invoke, fact .resolve, (call_iff g.outerLookup g.outerAlloc).mp h⟩
  | invoke => exact ⟨_, fact .enter, (enter_iff g).mp h⟩
  | inner phase =>
    obtain ⟨out, move, eq⟩ := (StraightLine.core_step_iff g.innerGuard ready).mp h
    exact ⟨.inner out, delegate move, eq⟩
  | args stack rest =>
    cases rest with
    | nil => exact (ready.1 rfl).elim
    | cons op rest =>
      obtain ⟨out, move, eq⟩ := eval_iff.mp h
      exact ⟨_, fact (.evaluate move), eq⟩
  | argumentTrap stack rest =>
    have nonempty : stack.map Value.toCore ≠ [] ∨ rest.map (site.emit coreSyntax) ≠ [] := by
      simpa [Admitted] using ready
    obtain ⟨mid, move, eq⟩ := read_body (label_stays (head := .trap) (stack := stack.map Value.toCore)
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (fun _ => nonempty)) h
    obtain ⟨kept, rest, cut, rfl⟩ := (Prefix.core_discard_iff (f := site.toSite.frame) (site.emit coreSyntax)).mp move
    refine ⟨argumentTrap kept rest, fact (.discard cut), ?_⟩
    simp only [coreConfig, trap_code]
    exact eq

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Proofs.Core
