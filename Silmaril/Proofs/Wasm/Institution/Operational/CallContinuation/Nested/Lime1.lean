module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Lime1Head

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Proofs.Lime1

open Wasm.Lime1.Execution
open CallContinuation.Proofs.Lime1 (first first_prefix first_values wrapper_step frame_label_stays)
open Execution.Runtime (Frame FuncAddr Value AdminInstr)

private abbrev ct (addr : FuncAddr) (fn : CallFrame.Callee) := CallContinuation.limeCode addr fn

theorem sound {H : Type} {s : Store H} {caller outer : Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} {arity : Nat}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a b : State} (e : Edge fn arity a b) :
    Step CallFrame.limeNoHost (limeConfig s caller outer addr fn arity a)
      (limeConfig s caller outer addr fn arity b) := by
  cases invert e with
  | context move => exact .frame (.label (CallContinuation.lime_sound allocated move) arity []) arity caller
  | ground h =>
    cases h with
    | labelValues stack => exact .frame (.pure s outer (.labelDone arity [] stack)) arity caller
    | labelTrap => exact .frame (.pure s outer (.labelTrap arity [])) arity caller
    | frameValues stack h => exact .pure s caller (.frameDone arity outer stack h)
    | frameTrap => exact .pure s caller (.frameTrap arity outer)

private theorem mapped_values (xs : List Value) : xs.map value = values xs := rfl

private theorem read_values {q : CallContinuation.State} {addr : FuncAddr} {fn : CallFrame.Callee} {vs : List Value}
    (eq : ct addr fn q = values vs) : ∃ stack, q = .done stack ∧ values vs = values stack := by
  have seen := congrArg first eq
  cases q with
  | done stack => exact ⟨stack, rfl, eq.symm⟩
  | resume stack =>
    simp only [ct, CallContinuation.limeCode, CallContinuation.render, first_prefix, first_values] at seen
    simp [first, asValue?] at seen
  | trapped stack hasTail =>
    simp only [ct, CallContinuation.limeCode, CallContinuation.render, List.append_assoc,
      List.singleton_append, first_prefix, first_values] at seen
    simp [first, asValue?] at seen
  | active phase =>
    cases phase <;>
      simp only [ct, CallContinuation.limeCode, CallContinuation.render, CallFrame.limeCode,
        CallFrame.legacyCode, mapped_values, List.append_assoc, List.singleton_append, first_prefix,
        first_values] at seen <;> simp [first, asValue?] at seen

private theorem read_trap {q : CallContinuation.State} {addr : FuncAddr} {fn : CallFrame.Callee}
    (eq : ct addr fn q = [.trap]) : q = .trapped [] false := by
  have seen := congrArg first eq
  cases q with
  | done stack =>
    simp only [ct, CallContinuation.limeCode, CallContinuation.render, first_values] at seen
    cases seen
  | resume stack =>
    simp only [ct, CallContinuation.limeCode, CallContinuation.render, first_prefix] at seen
    simp [first, asValue?] at seen
  | trapped stack hasTail =>
    have len := congrArg List.length eq
    cases hasTail <;>
      simp [ct, CallContinuation.limeCode, CallContinuation.render, CallContinuation.tail] at len
    subst stack
    rfl
  | active phase =>
    have len := congrArg List.length eq
    cases phase with
    | trapped stack =>
      simp [ct, CallContinuation.limeCode, CallContinuation.render, CallFrame.limeCode,
        CallFrame.legacyCode] at len
    | _ =>
      simp only [ct, CallContinuation.limeCode, CallContinuation.render, CallFrame.limeCode,
        CallFrame.legacyCode, mapped_values, List.append_assoc, List.singleton_append, first_prefix] at seen
      simp [first, asValue?] at seen

private theorem allowed {addr : FuncAddr} {fn : CallFrame.Callee} {q : CallContinuation.State}
    {op : Admin} (member : op ∈ ct addr fn q) :
    op ≠ .source .return_ ∧ ∀ l, op ≠ .source (.br l) := by
  have value_ok (xs : List Value) (a : Admin) (mem : a ∈ values xs) :
      a ≠ .source .return_ ∧ ∀ l, a ≠ .source (.br l) := by
    obtain ⟨⟨ty, bits⟩, _, rfl⟩ := List.mem_map.mp mem
    cases ty <;> simp [value]
  have append_ok {xs ys : List Admin} (ok : ∀ a ∈ ys, a ≠ .source .return_ ∧ ∀ l, a ≠ .source (.br l))
      (mem : op ∈ xs ++ ys) (first : ∀ a ∈ xs, a ≠ .source .return_ ∧ ∀ l, a ≠ .source (.br l)) :
      op ≠ .source .return_ ∧ ∀ l, op ≠ .source (.br l) :=
    (List.mem_append.mp mem).elim (first op) (ok op)
  cases q with
  | done stack => exact value_ok stack _ member
  | resume stack => exact append_ok (by simp) member (value_ok stack)
  | trapped stack hasTail =>
    cases hasTail <;>
      simp only [ct, CallContinuation.limeCode, CallContinuation.render, CallContinuation.tail,
        Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc] at member <;>
      exact append_ok (by simp) member (value_ok stack)
  | active phase =>
    cases phase <;>
      simp only [ct, CallContinuation.limeCode, CallContinuation.render, CallFrame.limeCode,
        CallFrame.legacyCode, mapped_values, List.append_assoc] at member <;>
      exact append_ok (by simp) member (value_ok _)

private theorem label_pop {types : List Wasm.Lime1.FuncType} {arity : Nat}
    {addr : FuncAddr} {fn : CallFrame.Callee} {q : CallContinuation.State} {out : List Admin}
    (h : PureStep types [.label arity [] (ct addr fn q)] out) :
    ∃ r, Ground arity (.label q) (.exit r) ∧ out = resultCode values .trap r := by
  generalize eq : ([.label arity [] (ct addr fn q)] : List Admin) = before at h
  cases h with
  | labelDone n cont vs =>
    obtain ⟨rfl, rfl, body⟩ := AdminInstr.label.inj (List.cons.inj eq).1
    obtain ⟨stack, rfl, read⟩ := read_values body
    exact ⟨.values stack, .labelValues stack, read⟩
  | labelTrap n cont =>
    have body := (AdminInstr.label.inj (List.cons.inj eq).1).2.2
    have same := read_trap body
    subst q
    exact ⟨.trap, .labelTrap, rfl⟩
  | labelBranch n cont pre kept tail len =>
    have body := (AdminInstr.label.inj (List.cons.inj eq).1).2.2
    exact ((allowed (q := q) (addr := addr) (fn := fn) (op := .source (.br ⟨0⟩)) (by rw [body]; simp)).2 ⟨0⟩ rfl).elim
  | labelBranchOuter n cont stack tail l bound =>
    have body := (AdminInstr.label.inj (List.cons.inj eq).1).2.2
    exact ((allowed (q := q) (addr := addr) (fn := fn) (op := .source (.br l)) (by rw [body]; simp)).2 l rfl).elim
  | labelReturn n cont stack tail =>
    have body := (AdminInstr.label.inj (List.cons.inj eq).1).2.2
    exact ((allowed (q := q) (addr := addr) (fn := fn) (op := .source .return_) (by rw [body]; simp)).1 rfl).elim
  | trapValues | trapTail =>
    have len := congrArg List.length eq
    simp [values] at len
  | _ =>
    have last := congrArg List.getLast? eq
    simp [values, List.getLast?_append] at last

private theorem frame_pop {types : List Wasm.Lime1.FuncType} {n : Nat} {f : Frame}
    {r : Result} {out : List Admin} (h : PureStep types [.frame n f (resultCode values .trap r)] out) :
    Ground n (.exit r) (.done r) ∧ out = resultCode values .trap r := by
  generalize eq : ([.frame n f (resultCode values .trap r)] : List Admin) = before at h
  cases h with
  | frameDone arity inner vs len =>
    obtain ⟨rfl, rfl, code⟩ := AdminInstr.frame.inj (List.cons.inj eq).1
    cases r with
    | values stack =>
      have count := congrArg List.length code
      simp only [resultCode, values_length, len] at count
      exact ⟨.frameValues stack count, code.symm⟩
    | trap =>
      have seen := congrArg first code
      simp [resultCode, first_values] at seen
      cases seen
  | frameReturn arity inner saved vs tail len =>
    have code := (AdminInstr.frame.inj (List.cons.inj eq).1).2.2
    have seen := congrArg first code
    cases r <;>
      simp only [resultCode, List.append_assoc, List.singleton_append, first_prefix, first_values] at seen <;>
      simp [first, asValue?] at seen
  | frameTrap arity inner =>
    have code := (AdminInstr.frame.inj (List.cons.inj eq).1).2.2
    cases r with
    | values stack =>
      have seen := congrArg first code
      simp only [resultCode, first_values] at seen
      cases seen
    | trap => exact ⟨.frameTrap, rfl⟩
  | trapValues | trapTail =>
    have len := congrArg List.length eq
    simp [values] at len
  | _ =>
    have last := congrArg List.getLast? eq
    simp [values, List.getLast?_append] at last

theorem result_stuck {H : Type} {s : Store H} {f : Frame} {r : Result} {b : Config H}
    (step : Step CallFrame.limeNoHost ⟨s, f, resultCode values .trap r⟩ b) : False := by
  cases r with
  | values stack =>
    obtain ⟨op, member, none⟩ := step.nonvalue
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp (show op ∈ values stack from member)
    simp at none
  | trap =>
    have h := CallContinuation.Proofs.Lime1.front step (vs := []) (rest := []) .trap rfl
    generalize stackEq : ([] : List Value) = stack at h
    generalize tailEq : ([] : List Admin) = tail at h
    cases h with
    | normal _ noTrap _ => exact noTrap rfl
    | bubble kept removed cut rest nz =>
      have removed : removed = [] := (List.append_eq_nil_iff.mp stackEq.symm).2
      have cut : cut = [] := (List.append_eq_nil_iff.mp tailEq.symm).1
      cases nz with
      | inl ne => exact ne removed
      | inr ne => exact ne cut

theorem label_result {types : List Wasm.Lime1.FuncType} {arity : Nat} {r : Result} {out : List Admin}
    (pop : PureStep types [.label arity [] (resultCode values .trap r)] out) :
    out = resultCode values .trap r := by
  generalize eq : ([.label arity [] (resultCode values .trap r)] : List Admin) = before at pop
  cases pop with
  | labelDone n cont vs =>
    have body := (AdminInstr.label.inj (List.cons.inj eq).1).2.2
    exact body.symm
  | labelTrap n cont =>
    have body := (AdminInstr.label.inj (List.cons.inj eq).1).2.2
    exact body.symm
  | labelBranch | labelBranchOuter | labelReturn =>
    have body := (AdminInstr.label.inj (List.cons.inj eq).1).2.2
    have seen := congrArg first body
    cases r <;>
      simp only [resultCode, List.append_assoc, List.singleton_append, first_prefix, first_values] at seen <;>
      simp [first, asValue?] at seen
  | trapValues | trapTail =>
    have len := congrArg List.length eq
    simp [values] at len
  | _ =>
    have last := congrArg List.getLast? eq
    simp [values, List.getLast?_append] at last

theorem frame_result {H : Type} {s : Store H} {caller outer : Frame} {arity : Nat} {r : Result}
    {dst : Config H} (step : Step CallFrame.limeNoHost ⟨s, caller, [.frame arity outer (resultCode values .trap r)]⟩ dst) :
    dst = ⟨s, caller, resultCode values .trap r⟩ := by
  cases wrapper_step step rfl trivial with
  | frame inner => exact (result_stuck inner).elim
  | pure pop => rw [(frame_pop pop).2]

theorem readback {H : Type} {s : Store H} {caller outer : Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} {arity : Nat}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {dst : Config H} (guard : Admitted fn a)
    (step : Step CallFrame.limeNoHost (limeConfig s caller outer addr fn arity a) dst) :
    ∃ out, Edge fn arity a out ∧ dst = limeConfig s caller outer addr fn arity out := by
  cases a with
  | done r => exact (result_stuck step).elim
  | exit r =>
    cases wrapper_step step rfl trivial with
    | frame inner => exact (result_stuck inner).elim
    | pure pop =>
      obtain ⟨rule, rfl⟩ := frame_pop pop
      exact ⟨.done r, fact rule, rfl⟩
  | label q =>
    cases wrapper_step step rfl trivial with
    | pure pop => exact (frame_label_stays pop).elim
    | frame outerStep =>
      cases wrapper_step outerStep rfl trivial with
      | pure pop =>
        obtain ⟨r, rule, rfl⟩ := label_pop pop
        exact ⟨.exit r, fact rule, rfl⟩
      | label actual =>
        obtain ⟨out, move, rfl⟩ := (CallContinuation.lime_step_iff (caller := outer) allocated guard).mp actual
        exact ⟨.label out, underLabel move, rfl⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Proofs.Lime1
