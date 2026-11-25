module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Thms
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Lime1Head

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame FuncAddr Value)

private abbrev nop : Admin := .source .nop

private theorem append_render (addr : FuncAddr) (fn : CallFrame.Callee) (q : CallFrame.State) :
    CallFrame.limeCode addr fn q ++ [nop] = limeCode addr fn (attach q) := by
  cases q <;> rfl

theorem sound {H : Type} {s : Store H} {caller : Frame} {addr : FuncAddr} {fn : CallFrame.Callee}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a b : State} (edge : Edge fn a b) :
    Step CallFrame.limeNoHost (limeConfig s caller addr fn a) (limeConfig s caller addr fn b) := by
  cases invert edge with
  | @call a b _ h =>
    have step := CallFrame.lime_sound (caller := caller) allocated h
    change Step CallFrame.limeNoHost ⟨s, caller, CallFrame.limeCode addr fn a ++ [nop]⟩
      ⟨s, caller, limeCode addr fn (attach b)⟩
    rw [← append_render]
    exact .context step [] [nop]
  | ground h =>
    cases h with
    | resume stack =>
      simpa only [limeConfig, limeCode, render, List.append_nil] using
        (Step.context (Step.pure (host := CallFrame.limeNoHost) s caller .nop) stack [])
    | discardValues kept removed hasTail ne =>
      cases removed with
      | nil => contradiction
      | cons v vs =>
        have h := Step.pure (host := CallFrame.limeNoHost) s caller (PureStep.trapValues v vs [])
        simpa only [limeConfig, limeCode, render, values_append, List.append_assoc, List.append_nil] using
          Step.context h kept (tail nop hasTail)
    | discardTail kept removed =>
      cases removed with
      | nil =>
        simpa only [limeConfig, limeCode, render, tail, ↓reduceIte, Bool.false_eq_true,
          List.append_nil, List.append_assoc, List.singleton_append] using
          (Step.context (Step.pure (host := CallFrame.limeNoHost) s caller (.trapTail nop [])) kept [])
      | cons v vs =>
        have h := Step.pure (host := CallFrame.limeNoHost) s caller (PureStep.trapValues v vs [nop])
        simpa only [limeConfig, limeCode, render, tail, ↓reduceIte, Bool.false_eq_true,
          List.append_nil, values_append, List.append_assoc] using Step.context h kept []

private theorem Front.ordinary {H : Type} {s : Store H} {f : Frame} {vs : List Value} {op : Admin}
    {rest : List Admin} {dst : Config H} (h : Front s f vs op rest dst)
    (notNop : op ≠ .source .nop) (notTrap : op ≠ .trap) :
    ∃ mid, Step CallFrame.limeNoHost ⟨s, f, values vs ++ [op]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, mid.code ++ rest⟩ := by
  cases h with
  | normal _ _ h => exact ⟨_, h, rfl⟩
  | nop => exact (notNop rfl).elim
  | bubble => exact (notTrap rfl).elim

theorem invoke_strip_suffix {H : Type} {s : Store H} {f : Frame} {a : FuncAddr}
    {stack : List Value} {rest : List Admin} {dst : Config H}
    (step : Step CallFrame.limeNoHost ⟨s, f, values stack ++ .invoke a :: rest⟩ dst) :
    ∃ mid, Step CallFrame.limeNoHost ⟨s, f, values stack ++ [.invoke a]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, mid.code ++ rest⟩ :=
  (front step (.invoke a) rfl).ordinary (by simp) (by simp)

theorem frame_context_inv {H : Type} {s : Store H} {f inside : Frame} {n : Nat}
    {saved : List Value} {code rest : List Admin} {dst : Config H}
    (step : Step CallFrame.limeNoHost ⟨s, f, values saved ++ .frame n inside code :: rest⟩ dst) :
    ∃ mid, Step CallFrame.limeNoHost ⟨s, f, [.frame n inside code]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values saved ++ mid.code ++ rest⟩ := by
  obtain ⟨mid, step, eq⟩ := (front step (.frame n inside code) rfl).ordinary (by simp) (by simp)
  obtain ⟨localStep, isolated, rfl⟩ := CallFrame.lime_frame_prefix_inv step
  exact ⟨localStep, isolated, eq⟩

theorem label_context_cases {H : Type} {s : Store H} {f : Frame} {n : Nat}
    {saved : List Value} {code rest : List Admin} {dst : Config H}
    (step : Step CallFrame.limeNoHost ⟨s, f, values saved ++ .label n [] code :: rest⟩ dst) :
    (∃ mid, Step CallFrame.limeNoHost ⟨s, f, code⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values saved ++ .label n [] mid.code :: rest⟩) ∨
    ∃ out, PureStep f.module.types [.label n [] code] out ∧ dst = ⟨s, f, values saved ++ out ++ rest⟩ := by
  obtain ⟨mid, move, rfl⟩ := (front step (.label n code) rfl).ordinary (by simp) (by simp)
  rcases CallFrame.lime_label_prefix_cases move with ⟨inner, h, rfl⟩ | ⟨out, pop, rfl⟩
  · exact .inl ⟨inner, h, by simp only [List.append_assoc, List.singleton_append]⟩
  · exact .inr ⟨out, pop, rfl⟩

theorem active_strip {H : Type} {s : Store H} {caller : Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} {a : CallFrame.State} {dst : Config H}
    {suffix : List Admin} (live : Active a) (step : Step CallFrame.limeNoHost (⟨s, caller, CallFrame.limeCode addr fn a ++ suffix⟩) dst) :
    ∃ mid, Step CallFrame.limeNoHost (CallFrame.limeConfig s caller addr fn a) mid ∧
      dst = ⟨mid.store, mid.frame, mid.code ++ suffix⟩ := by
  have strip {op : Admin} {stack : List Value} (focus : Focus op)
      (noNop : op ≠ .source .nop) (noTrap : op ≠ .trap)
      (code : CallFrame.limeCode addr fn a = values stack ++ [op]) :
      ∃ mid, Step CallFrame.limeNoHost (CallFrame.limeConfig s caller addr fn a) mid ∧
        dst = ⟨mid.store, mid.frame, mid.code ++ suffix⟩ := by
    have source : (⟨s, caller, CallFrame.limeCode addr fn a ++ suffix⟩ : Config H).code = values stack ++ op :: suffix := by
      change CallFrame.limeCode addr fn a ++ suffix = _
      rw [code, List.append_assoc, List.singleton_append]
    obtain ⟨mid, h, eq⟩ := (front step focus source).ordinary noNop noTrap
    refine ⟨mid, ?_, eq⟩
    change Step CallFrame.limeNoHost ⟨s, caller, CallFrame.limeCode addr fn a⟩ mid
    rw [code]
    exact h
  cases a with
  | invoke saved args => exact strip (.invoke addr) (by intro h; cases h) (by intro h; cases h) rfl
  | label saved ls body => exact strip (.frame _ _ _) (by intro h; cases h) (by intro h; cases h) rfl
  | exit saved ls ready => exact strip (.frame _ _ _) (by intro h; cases h) (by intro h; cases h) rfl
  | returned | trapped => exact live.elim

private theorem trap_read {H : Type} {s : Store H} {caller : Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} {vs : List Value} {hasTail : Bool} {dst : Config H}
    (step : Step CallFrame.limeNoHost (limeConfig s caller addr fn (.trapped vs hasTail)) dst) :
    ∃ out, Edge fn (.trapped vs hasTail) out ∧ dst = limeConfig s caller addr fn out := by
  have shape := front step (vs := vs) (rest := tail nop hasTail) Focus.trap
    (by simp only [limeConfig, limeCode, render, List.append_assoc, List.singleton_append])
  generalize eq : tail nop hasTail = rest at shape
  cases shape with
  | normal _ noTrap _ => exact (noTrap rfl).elim
  | bubble kept removed cut rest nz =>
    cases cut with
    | nil =>
      have ne := nz.resolve_right (fun h => h rfl)
      exact ⟨.trapped kept hasTail, fact (.discardValues kept removed hasTail ne), by
        simp only [List.nil_append] at eq
        rw [← eq]
        simp only [limeConfig, limeCode, render, List.append_assoc, List.singleton_append]⟩
    | cons op cut =>
      cases hasTail
      · simp [tail] at eq
      · simp [tail] at eq
        obtain ⟨_, rfl, rfl⟩ := eq
        exact ⟨.trapped kept false, fact (.discardTail kept removed), by simp [limeConfig, limeCode, render, tail]⟩

theorem readback {H : Type} {s : Store H} {caller : Frame} {addr : FuncAddr} {fn : CallFrame.Callee}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {dst : Config H} (ready : Admitted fn a)
    (step : Step CallFrame.limeNoHost (limeConfig s caller addr fn a) dst) :
    ∃ out, Edge fn a out ∧ dst = limeConfig s caller addr fn out := by
  cases a with
  | active q =>
    obtain ⟨mid, h, rfl⟩ := active_strip (suffix := [nop]) ready.1 step
    obtain ⟨out, edge, rfl⟩ := (CallFrame.lime_step_iff allocated ready.2).mp h
    exact ⟨attach out, call ready.1 edge, congrArg (fun code => (⟨s, caller, code⟩ : Config H))
      (append_render addr fn out)⟩
  | done stack =>
    obtain ⟨x, mem, hx⟩ := step.nonvalue
    change x ∈ values stack at mem
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp mem
    simp at hx
  | resume stack =>
    cases front step (vs := stack) (rest := []) Focus.nop rfl with
    | normal h _ _ => exact (h rfl).elim
    | nop => exact ⟨.done stack, fact (.resume stack), by simp [limeConfig, limeCode, render]⟩
  | trapped stack hasTail => exact trap_read step

end Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs.Lime1
