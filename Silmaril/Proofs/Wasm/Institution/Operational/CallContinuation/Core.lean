module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Thms
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs

open Execution
open Execution.Core
open Execution.Runtime (FuncAddr Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det

private abbrev cv (vs : List Value) := vals (vs.map Value.toCore)
private abbrev nop : Admin := .plain .nop

private theorem append_render (addr : FuncAddr) (fn : CallFrame.Callee) (q : CallFrame.State) :
    CallFrame.coreCode addr fn q ++ [nop] = coreCode addr fn (attach q) := by
  cases q <;> rfl

theorem core_sound {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a b : State} (edge : Edge fn a b) :
    Step P noHost (coreConfig s caller addr fn a) (coreConfig s caller addr fn b) := by
  cases invert edge with
  | @call a b _ h =>
    have step := CallFrame.core_sound (P := P) (caller := caller) allocated h
    change Step P noHost ⟨s, caller.toCore, CallFrame.coreCode addr fn a ++ [nop]⟩
      ⟨s, caller.toCore, coreCode addr fn (attach b)⟩
    rw [← append_render]
    exact Core.Sim.Step.append_right step [nop]
  | ground h =>
    cases h with
    | resume stack => simpa only [coreConfig, coreCode, render, List.append_nil] using
        (lift_instrs (P := P) (H := H) (stack.map Value.toCore) [] _ _ (.parametric (s := s)
          (f := caller.toCore) .nop))
    | discardValues kept removed hasTail h =>
      have step := Step.trapInstrs (P := P) (host := noHost) (s := s) (f := caller.toCore)
        (vs := removed.map Value.toCore) (rest := []) (.inl (by simpa using h))
      have lifted := lift_instrs (kept.map Value.toCore) (tail nop hasTail) _ _ step
      simpa only [coreConfig, coreCode, render, List.map_append, vals_append, List.append_assoc,
        List.append_nil] using lifted
    | discardTail kept removed =>
      have step := Step.trapInstrs (P := P) (host := noHost) (s := s) (f := caller.toCore)
        (vs := removed.map Value.toCore) (rest := [nop]) (.inr (by decide))
      have lifted := lift_instrs (kept.map Value.toCore) [] _ _ step
      simpa only [coreConfig, coreCode, render, tail, Bool.true_eq, ↓reduceIte, Bool.false_eq_true,
        List.map_append, vals_append, List.append_assoc, List.append_nil] using lifted

theorem active_strip {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a : CallFrame.State} {dst : Config H} {suffix : List Admin} (live : Active a)
    (step : Step P noHost (⟨s, caller.toCore, CallFrame.coreCode addr fn a ++ suffix⟩) dst) :
    ∃ mid, Step P noHost (CallFrame.coreConfig s caller addr fn a) mid ∧
      dst = ⟨mid.store, mid.frame, mid.code ++ suffix⟩ := by
  cases a with
  | invoke saved args =>
    simp only [CallFrame.coreCode, List.append_assoc] at step
    obtain ⟨kept, used, ps, rs, stack, hexpand, arity, rfl⟩ :=
      Step.callRef_wasm_inv_seq (vs := (saved ++ args).map Value.toCore)
        (r := .callRefType fn.type.toDefType) (rest := suffix)
        (by trivial) allocated (show fn.coreInstance.code = .wasm fn.coreFunc from rfl) step
    let body : List Admin := [.label rs.length [] (expression fn.coreFunc.body)]
    let run := Admin.frame rs.length (Frame.forCall (fn.coreInstance (H := H)).module used fn.coreFunc.locals) body
    refine ⟨⟨s, caller.toCore, vals kept ++ [run]⟩, ?_, by simp [run, body]⟩
    change Step P noHost ⟨s, caller.toCore, vals ((saved ++ args).map Value.toCore) ++ _⟩ _
    rw [stack, vals_append, List.append_assoc]
    simpa only [List.append_nil] using
      lift_instrs kept [] _ _ (.callRefFunc (c := .callRefType fn.type.toDefType)
        (by trivial) allocated hexpand arity rfl)
  | label saved ls body =>
    simp only [CallFrame.coreCode, List.append_assoc,
      List.singleton_append] at step
    obtain ⟨mid, h, eq⟩ := Step.ctx_in_seq (vs := saved.map Value.toCore) (rest := suffix)
      (X := .frame fn.arity (fn.frame ls).toCore [.label fn.arity [] (CallFrame.coreBody body)])
      (by trivial) step
    exact ⟨⟨mid.store, mid.frame, cv saved ++ mid.code⟩, by
      simpa only [CallFrame.coreConfig, CallFrame.coreCode, List.append_nil] using lift_instrs
        (saved.map Value.toCore) [] _ _ h, eq⟩
  | exit saved ls ready =>
    simp only [CallFrame.coreCode, List.append_assoc,
      List.singleton_append] at step
    obtain ⟨mid, h, eq⟩ := Step.ctx_in_seq (vs := saved.map Value.toCore) (rest := suffix)
      (X := .frame fn.arity (fn.frame ls).toCore (CallFrame.coreExit ready)) (by trivial) step
    exact ⟨⟨mid.store, mid.frame, cv saved ++ mid.code⟩, by
      simpa only [CallFrame.coreConfig, CallFrame.coreCode, List.append_nil] using lift_instrs
        (saved.map Value.toCore) [] _ _ h, eq⟩
  | returned | trapped => exact live.elim

private theorem trap_read {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} {vs : List Value} {hasTail : Bool} {dst : Config H}
    (step : Step P noHost (coreConfig s caller addr fn (.trapped vs hasTail)) dst) :
    ∃ out, Edge fn (.trapped vs hasTail) out ∧ dst = coreConfig s caller addr fn out := by
  change Step P noHost ⟨s, caller.toCore, cv vs ++ [.trap] ++ tail nop hasTail⟩ dst at step
  have headEq : fnv (cv vs ++ [.trap] ++ tail nop hasTail) =
      (vs.map Value.toCore, .trap :: tail nop hasTail) := by simp [List.append_assoc]
  rcases Wasm.SingleThreaded.Det.Step.decomp step with head | bubble
  · obtain ⟨_, _, op, _, _, head, _, h, _⟩ := fnv_headDec head
    rw [headEq] at head
    exact (h.good.ne_trap (List.cons.inj (congrArg Prod.snd head)).1.symm).elim
  · obtain ⟨kept, removed, cut, rest, nz, ⟨head, _, rfl⟩ | ⟨_, head, _, _⟩⟩ := fnv_bubble bubble
    · rw [headEq] at head
      simp only [Prod.mk.injEq, List.cons.injEq] at head
      obtain ⟨values, suff⟩ := head
      obtain ⟨before, discarded, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp values
      cases cut with
      | nil =>
        have ne : discarded ≠ [] := by
          intro bad
          simp [bad] at nz
        exact ⟨.trapped before hasTail, fact (.discardValues before discarded hasTail ne),
          by simp only [List.nil_append] at suff; rw [← suff.2]; rfl⟩
      | cons op cut =>
        cases hasTail with
        | false => simp [tail] at suff
        | true =>
          simp [tail] at suff
          obtain ⟨_, rfl, rfl⟩ := suff
          exact ⟨.trapped before false, fact (.discardTail before discarded), rfl⟩
    · rw [headEq] at head
      simp at head

theorem core_readback {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a : State} {dst : Config H} (ready : Admitted fn a)
    (step : Step P noHost (coreConfig s caller addr fn a) dst) :
    ∃ out, Edge fn a out ∧ dst = coreConfig s caller addr fn out := by
  cases a with
  | active q =>
    obtain ⟨mid, h, rfl⟩ := active_strip (suffix := [nop]) allocated ready.1 step
    obtain ⟨out, edge, rfl⟩ := (CallFrame.core_step_iff allocated ready.2).mp h
    exact ⟨attach out, call ready.1 edge, congrArg (fun code => (⟨s, caller.toCore, code⟩ : Config H))
      (append_render addr fn out)⟩
  | done stack => exact (Step.not_vals step).elim
  | resume stack =>
    change Step P noHost ⟨s, caller.toCore, cv stack ++ [nop]⟩ dst at step
    rcases Wasm.SingleThreaded.Det.Step.decomp step with head | bubble
    · obtain ⟨kept, args, op, rest, mid, source, _, h, rfl⟩ := fnv_headDec head
      simp only [fnv_vals_append, fnv_cons_of_none (a := nop) rfl, Prod.mk.injEq, List.cons.injEq] at source
      obtain ⟨stackEq, rfl, rfl⟩ := source
      have fam := h.fam_inv (by decide)
      obtain ⟨_, pure, rfl⟩ := fam
      generalize eq : vals args ++ [nop] = before at pure
      have last := congrArg List.getLast? eq
      cases pure with
      | nop =>
        have empty : args = [] := by simpa [vals] using congrArg List.length eq
        subst args
        simp only [List.append_nil] at stackEq
        exact ⟨.done stack, fact (.resume stack), by rw [← stackEq]; simp [coreConfig, coreCode, render]⟩
      | _ => simp [List.getLast?_append] at last
    · obtain ⟨_, _, _, _, _, ⟨head, _, _⟩ | ⟨_, head, _, _⟩⟩ := fnv_bubble bubble <;>
        simp [fnv_cons_of_none (a := nop) rfl] at head
  | trapped stack hasTail => exact trap_read step

theorem frame_label_stays {H : Type} {s : Store H} {f : Frame} {arity : Nat}
    {k : Nat} {cont : List Instr} {body out : List Admin} (h : FrameExit s f arity [.label k cont body] out) : False := by
  generalize eq : ([.label k cont body] : List Admin) = code at h
  cases h with
  | returnCallNull kind | returnCallAddr kind _ _ _ =>
    have first := congrArg (fun code => (fnv code).2) eq
    have none := Admin.val?_of_isReturnCallRef kind
    simp [fnv_cons_of_none none, fnv_cons_of_none (a := .label k cont body) rfl] at first
    rw [← first.1] at kind
    contradiction
  | _ =>
    have first := congrArg (fun code => (fnv code).2) eq
    simp [fnv_cons_of_none (a := .label k cont body) rfl,
      fnv_cons_of_none (a := .plain .return_) rfl, fnv_cons_of_none (a := .plain .throwRef) rfl, throwing] at first

end Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs
