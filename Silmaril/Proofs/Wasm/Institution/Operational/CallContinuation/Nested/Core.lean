module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Proofs

open Execution.Core
open Execution.Runtime (FuncAddr Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det

private abbrev cv (vs : List Value) := vals (vs.map Value.toCore)
private abbrev ct (addr : FuncAddr) (fn : CallFrame.Callee) := CallContinuation.coreCode addr fn

theorem core_sound {H : Type} {P : Profile} {s : Store H} {caller outer : Execution.Runtime.Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} {arity : Nat}
    (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a b : State} (e : Edge fn arity a b) :
    Step P noHost (coreConfig s caller outer addr fn arity a)
      (coreConfig s caller outer addr fn arity b) := by
  cases invert e with
  | context move => exact .ctxtFrame (.ctxtLabel (CallContinuation.core_sound allocated move))
  | ground h =>
    cases h with
    | labelValues stack => exact .ctxtFrame .labelVals
    | labelTrap => exact .ctxtFrame .trapLabel
    | frameValues stack h => exact .frameVals (by simpa using h)
    | frameTrap => exact .trapFrame

private def safe (op : Admin) : Prop :=
  op ≠ .plain .return_ ∧ op ≠ .plain .throwRef ∧ (∀ idx, op ≠ .plain (.br idx)) ∧ ¬ op.IsReturnCallRef

private theorem safe_value (v : Val) : safe v.toAdmin := by
  rcases v with ⟨⟨t, bits⟩⟩ | _ | _
  · cases t <;> simp [safe, Val.toAdmin, Admin.IsReturnCallRef]
  · simp [safe, Val.toAdmin, Admin.IsReturnCallRef]
  · simp [safe, Val.toAdmin, Admin.IsReturnCallRef]

private theorem safe_values (xs : List Val) {op : Admin} (mem : op ∈ vals xs) : safe op := by
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp mem
  exact safe_value v

private theorem body_safe (addr : FuncAddr) (fn : CallFrame.Callee) (q : CallContinuation.State)
    {op : Admin} (member : op ∈ ct addr fn q) : safe op := by
  have appended {xs ys : List Admin} (h₁ : ∀ a ∈ xs, safe a) (h₂ : ∀ a ∈ ys, safe a)
      (ha : op ∈ xs ++ ys) : safe op :=
    (List.mem_append.mp ha).elim (h₁ op) (h₂ op)
  cases q with
  | done stack => exact safe_values _ member
  | resume stack =>
    exact appended (fun _ => safe_values _) (by simp [safe, Admin.IsReturnCallRef]) member
  | trapped stack hasTail =>
    cases hasTail <;>
      simp only [CallContinuation.coreCode, CallContinuation.render, CallContinuation.tail,
        Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc] at member <;>
      exact appended (fun _ => safe_values _) (by simp [safe, Admin.IsReturnCallRef]) member
  | active a =>
    cases a <;>
      simp only [CallContinuation.coreCode, CallContinuation.render, CallFrame.coreCode,
        List.append_assoc] at member <;>
      exact appended (fun _ => safe_values _) (by simp [safe, Admin.IsReturnCallRef]) member

private theorem read_values {q : CallContinuation.State} {addr : FuncAddr} {fn : CallFrame.Callee} {vs : List Val}
    (eq : ct addr fn q = vals vs) : ∃ stack, q = .done stack ∧ vals vs = cv stack := by
  have residual := congrArg (fun code => (fnv code).2) eq
  cases q with
  | done stack => exact ⟨stack, rfl, eq.symm⟩
  | resume stack =>
    simp [ct, CallContinuation.coreCode, CallContinuation.render,
      fnv_cons_of_none (a := .plain .nop) rfl] at residual
  | trapped stack hasTail =>
    simp [ct, CallContinuation.coreCode, CallContinuation.render, List.append_assoc,
      fnv_cons_of_none (a := .trap) rfl] at residual
  | active a =>
    cases a <;>
      simp [ct, CallContinuation.coreCode, CallContinuation.render, CallFrame.coreCode,
        List.append_assoc, fnv_cons_of_none (a := .plain .nop) rfl,
        fnv_cons_of_none (a := .trap) rfl, fnv_cons_of_none (a := .callRefType fn.type.toDefType) rfl,
        fnv_cons_of_none (a := .frame _ _ _) rfl] at residual

private theorem read_trap {q : CallContinuation.State} {addr : FuncAddr} {fn : CallFrame.Callee}
    (eq : ct addr fn q = [.trap]) : q = .trapped [] false := by
  have residual := congrArg (fun code => (fnv code).2) eq
  cases q with
  | done stack => simp [ct, CallContinuation.coreCode, CallContinuation.render] at residual
  | resume stack =>
    simp [ct, CallContinuation.coreCode, CallContinuation.render,
      fnv_cons_of_none (a := .plain .nop) rfl] at residual
  | trapped stack hasTail =>
    cases hasTail
    · have len := congrArg List.length eq
      simp [ct, CallContinuation.coreCode, CallContinuation.render, CallContinuation.tail, vals] at len
      subst stack
      rfl
    · simp [ct, CallContinuation.coreCode, CallContinuation.render, CallContinuation.tail, List.append_assoc,
        fnv_cons_of_none (a := .trap) rfl] at residual
  | active a =>
    cases a <;>
      simp [ct, CallContinuation.coreCode, CallContinuation.render, CallFrame.coreCode,
        List.append_assoc, fnv_cons_of_none (a := .plain .nop) rfl,
        fnv_cons_of_none (a := .trap) rfl, fnv_cons_of_none (a := .callRefType fn.type.toDefType) rfl,
        fnv_cons_of_none (a := .frame _ _ _) rfl] at residual

private theorem label_pop {addr : FuncAddr} {fn : CallFrame.Callee} {arity : Nat}
    {q : CallContinuation.State} {out : List Admin}
    (h : LabelExit arity [] (ct addr fn q) out) :
    ∃ result, Ground arity (.label q) (.exit result) ∧ out = resultCode cv .trap result := by
  have allowed : ∀ a ∈ ct addr fn q, safe a := fun _ => body_safe addr fn q
  generalize eq : ct addr fn q = code at h
  rw [eq] at allowed
  cases h with
  | vals vs =>
    obtain ⟨stack, rfl, read⟩ := read_values eq
    exact ⟨.values stack, .labelValues stack, read⟩
  | trap =>
    have same := read_trap eq
    subst q
    exact ⟨.trap, .labelTrap, rfl⟩
  | @brZero _ _ label _ _ _ | @brSucc _ label _ _ =>
      exact ((allowed (.plain (.br label)) (by simp)).2.2.1 label rfl).elim
  | ret => exact ((allowed (.plain .return_) (by simp)).1 rfl).elim
  | @returnCall vs op rest kind => exact ((allowed op (by simp)).2.2.2 kind).elim
  | throw a => exact ((allowed (.plain .throwRef) (by simp [throwing])).2.1 rfl).elim

private theorem frame_label_stays {H : Type} {s : Store H} {f : Frame} {arity : Nat}
    {body out : List Admin} (h : FrameExit s f arity [.label arity [] body] out) : False := by
  generalize eq : ([.label arity [] body] : List Admin) = code at h
  cases h with
  | returnCallNull kind | returnCallAddr kind _ _ _ =>
    have first := congrArg (fun code => (fnv code).2) eq
    have none := Admin.val?_of_isReturnCallRef kind
    simp [fnv_cons_of_none none, fnv_cons_of_none (a := .label arity [] body) rfl] at first
    rw [← first.1] at kind
    contradiction
  | _ =>
    have first := congrArg (fun code => (fnv code).2) eq
    simp [fnv_cons_of_none (a := .label arity [] body) rfl,
      fnv_cons_of_none (a := .plain .return_) rfl, fnv_cons_of_none (a := .plain .throwRef) rfl, throwing] at first

private theorem frame_pop {H : Type} {s : Store H} {f : Frame} {arity : Nat}
    {r : Result} {out : List Admin} (h : FrameExit s f arity (resultCode cv .trap r) out) :
    Ground arity (.exit r) (.done r) ∧ out = resultCode cv .trap r := by
  have allowed : ∀ a ∈ resultCode cv .trap r, safe a := by
    cases r with
    | values v => exact fun _ => safe_values _
    | trap => simp [resultCode, safe, Admin.IsReturnCallRef]
  generalize eq : resultCode cv .trap r = code at h
  rw [eq] at allowed
  cases h with
  | @vals vs len =>
    cases r with
    | values stack =>
      have sizes := congrArg List.length eq
      simp only [resultCode, vals, List.length_map, len] at sizes
      exact ⟨.frameValues stack sizes, rfl⟩
    | trap =>
      have residual := congrArg (fun code => (fnv code).2) eq
      simp [resultCode] at residual
  | trap =>
    cases r with
    | values stack =>
      have residual := congrArg (fun code => (fnv code).2) eq
      simp [resultCode] at residual
    | trap => exact ⟨.frameTrap, rfl⟩
  | ret => exact ((allowed (.plain .return_) (by simp)).1 rfl).elim
  | @returnCallNull _ op _ kind => exact ((allowed op (by simp)).2.2.2 kind).elim
  | @returnCallAddr _ _ _ op _ _ _ _ kind _ _ _ => exact ((allowed op (by simp)).2.2.2 kind).elim
  | throw a => exact ((allowed (.plain .throwRef) (by simp [throwing])).2.1 rfl).elim

private theorem no_result_step {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {r : Result} {dst : Config H} (h : Step P noHost ⟨s, f, resultCode cv .trap r⟩ dst) : False := by
  cases r with
  | values stack => exact Step.not_vals h
  | trap => exact Step.trap_stuck h

theorem core_readback {H : Type} {P : Profile} {s : Store H} {caller outer : Execution.Runtime.Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} {arity : Nat}
    (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a : State} {dst : Config H} (guard : Admitted fn a)
    (h : Step P noHost (coreConfig s caller outer addr fn arity a) dst) :
    ∃ out, Edge fn arity a out ∧ dst = coreConfig s caller outer addr fn arity out := by
  cases a with
  | done r => exact (no_result_step h).elim
  | exit r =>
    rcases Step.frame_inv h with ⟨_, _, _, step, _⟩ | ⟨_, pop, rfl⟩
    · exact (no_result_step step).elim
    · obtain ⟨rule, rfl⟩ := frame_pop pop
      exact ⟨.done r, fact rule, rfl⟩
  | label q =>
    rcases Step.frame_inv h with ⟨_, _, _, step, rfl⟩ | ⟨_, pop, _⟩
    · rcases Step.label_inv step with ⟨_, _, _, step, same⟩ | ⟨_, pop, same⟩
      · obtain ⟨out, move, eq⟩ := (CallContinuation.core_step_iff allocated guard).mp step
        let wrapLabel (c : Config H) : Config H := ⟨c.store, c.frame, [.label arity [] c.code]⟩
        let wrapFrame (c : Config H) : Config H := ⟨c.store, caller.toCore, [.frame arity c.frame c.code]⟩
        exact ⟨.label out, underLabel move, congrArg wrapFrame (same.trans (congrArg wrapLabel eq))⟩
      · obtain ⟨out, move, rfl⟩ := label_pop pop
        cases same
        exact ⟨.exit out, fact move, rfl⟩
    · exact (frame_label_stays pop).elim

end Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Proofs
