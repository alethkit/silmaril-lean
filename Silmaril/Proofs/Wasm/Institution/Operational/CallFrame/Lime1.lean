module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallFrame.Thms
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Sequence
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Lime1Head

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame.Proofs.Lime1

open Silmaril.Wasm.Lime1.Execution
open Silmaril.Wasm.Execution.Runtime

private abbrev bodyCode : Body → List Admin :=
  legacyBody Locals.limeInstr .return_ .unreachable

private abbrev exitCode : Exit → List Admin := legacyExit value .return_

private theorem encode_values (vs : List Value) :
    Locals.limeCodec.encode (Locals.values vs) = values vs := by
  have emit (v : Value) : Locals.limeCodec.emit (.value v) = value v := by
    rcases v with ⟨t, bits⟩
    cases t <;> rfl
  simp [Locals.Codec.encode, Locals.values, values, List.map_map, emit]

@[local simp] private theorem body_locals (code : List Locals.Op) :
    bodyCode (.code (.locals code)) = Locals.limeCodec.encode code := List.map_map

@[local simp] private theorem body_return (stack : List Value) :
    bodyCode (.code (.ret stack)) = values stack ++ [.source .return_] := by
  simp only [legacyBody, Program.instructions, List.map_append, List.map_cons, List.map_nil]
  rw [List.map_map, ← encode_values]
  rfl

private theorem context_step {H : Type} (saved : List Value) {a b : Config H}
    (h : Step limeNoHost a b) :
    Step limeNoHost ⟨a.store, a.frame, values saved ++ a.code⟩ ⟨b.store, b.frame, values saved ++ b.code⟩ := by
  cases a
  cases b
  simpa only [List.append_nil] using Step.context h saved []

theorem sound {H : Type} {s : Store H} {caller : Frame} {address : FuncAddr} {fn : Callee}
    (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a b : State} (step : Edge fn a b) :
    Step limeNoHost (limeConfig s caller address fn a) (limeConfig s caller address fn b) := by
  cases invert step with
  | @reduce saved before after h =>
    have inner := Locals.lime_sound (s := s) (m := fn.module) (host := limeNoHost) h
    simpa [limeConfig, limeCode, legacyCode, values, Callee.frame] using
      context_step saved (.frame (.label inner fn.arity []) fn.arity caller)
  | fact h =>
    cases h with
    | enter saved args arity =>
      have h := Step.invokeWasm (host := limeNoHost) s caller address fn.type fn.module fn.limeFunc
        args allocated arity
      simpa [limeConfig, limeCode, legacyCode, Callee.limeFunc, Callee.init, Callee.frame, Callee.type,
        Callee.arity, expression, values, List.map_append, List.append_assoc, legacyBody] using context_step saved h
    | unreachable saved ls =>
      have h := Step.pure (host := limeNoHost) s (fn.frame ls) PureStep.unreachable
      simpa [limeConfig, limeCode, legacyCode, legacyBody, Program.instructions, values] using
        context_step saved (.frame (.label h fn.arity []) fn.arity caller)
    | labelValues saved ls stack =>
      have h := Step.pure (host := limeNoHost) s (fn.frame ls) (PureStep.labelDone fn.arity [] stack)
      simpa [limeConfig, limeCode, legacyCode, legacyExit, encode_values, values] using
        context_step saved (.frame h fn.arity caller)
    | labelReturn saved ls stack =>
      have h := Step.pure (host := limeNoHost) s (fn.frame ls) (PureStep.labelReturn fn.arity [] stack [])
      simpa [limeConfig, limeCode, legacyCode, legacyExit, values] using
        context_step saved (.frame h fn.arity caller)
    | labelTrap saved ls =>
      have h := Step.pure (host := limeNoHost) s (fn.frame ls) (PureStep.labelTrap fn.arity [])
      simpa [limeConfig, limeCode, legacyCode, legacyBody, legacyExit, values] using
        context_step saved (.frame h fn.arity caller)
    | frameValues saved ls stack arity =>
      have h := Step.pure (host := limeNoHost) s caller (PureStep.frameDone fn.arity (fn.frame ls) stack arity)
      simpa [limeConfig, limeCode, legacyCode, legacyExit, values, List.map_append] using context_step saved h
    | frameReturn saved ls extra results arity =>
      have h := Step.pure (host := limeNoHost) s caller
        (PureStep.frameReturn fn.arity (fn.frame ls) extra results [] arity)
      simpa [limeConfig, limeCode, legacyCode, legacyExit, values, List.map_append, List.append_assoc] using
        context_step saved h
    | frameTrap saved ls =>
      have h := Step.pure (host := limeNoHost) s caller (PureStep.frameTrap fn.arity (fn.frame ls))
      simpa [limeConfig, limeCode, legacyCode, legacyExit, values] using context_step saved h
    | bubble saved discarded ne =>
      cases discarded with
      | nil => exact (ne rfl).elim
      | cons v vs =>
        have h := Step.pure (host := limeNoHost) s caller (PureStep.trapValues v vs [])
        simpa [limeConfig, limeCode, legacyCode, values, List.map_append, List.append_assoc] using context_step saved h

private theorem value_code_injective : Function.Injective (values : List Value → List Admin) :=
  stack_injective value asValue? asValue?_value

private theorem value_nonvalue {stack : List Value} {e : Admin} (hv : asValue? e = none)
    (h : e ∈ values stack) : False := by
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp h
  simp at hv

private theorem one_nonvalue {used actual : List Value} {e last : Admin} {tail : List Admin}
    (active : asValue? e = none) (eq : values used ++ [e] ++ tail = values actual ++ [last]) :
    actual = used ∧ e = last ∧ tail = [] := by
  obtain ⟨extra, stack, split, rfl⟩ := split_context value asValue? asValue?_value used actual
    (mid := [e]) (tail := tail) ⟨e, List.Mem.head _, active⟩ eq
  have len := congrArg List.length split
  simp at len
  subst extra
  exact ⟨by simpa using stack, (List.cons.inj split).1, rfl⟩

private theorem singleton_step {H : Type} {s : Store H} {f : Frame} {op : Admin}
    {dst : Config H} (focus : Focus op) (h : Step limeNoHost ⟨s, f, [op]⟩ dst) :
    HeadStep s f [] op dst := by
  obtain ⟨saved, used, mid, splitArgs, head, out⟩ := split h (stack := []) focus rfl
  obtain ⟨rfl, rfl⟩ := List.nil_eq_append_iff.mp splitArgs
  have eq : dst = mid := by simpa [values] using out
  subst dst
  exact head

private theorem frame_cases {H : Type} {s : Store H} {f inside : Frame} {n : Nat}
    {saved : List Value} {code : List Admin} {dst : Config H}
    (h : Step limeNoHost ⟨s, f, values saved ++ [.frame n inside code]⟩ dst) :
    (∃ s' inside' rest, Step limeNoHost ⟨s, inside, code⟩ ⟨s', inside', rest⟩ ∧
      dst = ⟨s', f, values saved ++ [.frame n inside' rest]⟩) ∨
    (∃ rest, PureFocus [] (.frame n inside code) rest ∧ dst = ⟨s, f, values saved ++ rest⟩) := by
  obtain ⟨kept, used, target, stackEq, head, rfl⟩ := split h (.frame n inside code) rfl
  cases head with
  | frame innerStep =>
    rw [List.append_nil] at stackEq
    subst kept
    exact .inl ⟨_, _, _, innerStep, rfl⟩
  | pure ordinary =>
    have exit := pure_focus ordinary (.frame n inside code)
    have zero : used = [] := by cases exit <;> rfl
    subst used
    rw [List.append_nil] at stackEq
    subst kept
    exact .inr ⟨_, exit, rfl⟩

private theorem label_pop {fn : Callee} (saved ls : List Value) {body : Body} {out : List Admin}
    (h : PureFocus [] (.label fn.arity [] (bodyCode body)) out) :
    ∃ ready, Ground fn (.label saved ls body) (.exit saved ls ready) ∧ out = exitCode ready := by
  generalize eq : bodyCode body = code at h
  cases h with
  | labelDone _ _ stack =>
    cases body with
    | trap => exact (value_nonvalue (e := .trap) rfl (by rw [← eq]; exact List.Mem.head _)).elim
    | code p =>
      cases p with
      | locals code =>
        have decode := congrArg Locals.limeCodec.decode (show Locals.limeCodec.encode code = values stack by simpa using eq)
        rw [← encode_values] at decode
        simp only [Locals.Codec.decode_encode] at decode
        subst code
        exact ⟨.values stack, .labelValues saved ls stack, rfl⟩
      | ret vals =>
        rw [body_return] at eq
        exact (value_nonvalue (e := .source .return_) rfl (by rw [← eq]; simp)).elim
      | unreachable =>
        exact (value_nonvalue (e := .source .unreachable) rfl (by rw [← eq]; exact List.Mem.head _)).elim
  | labelReturn _ _ stack tail =>
    have member : (.source .return_ : Admin) ∈ bodyCode body := by rw [eq]; simp
    cases body with
    | trap => simp [bodyCode, legacyBody] at member
    | code p =>
      cases p with
      | locals code =>
        have check := Locals.limeCodec.supports_encode code
        rw [← body_locals] at check
        exact Bool.noConfusion (check _ member)
      | ret actual =>
        rw [body_return] at eq
        obtain ⟨same, _, rfl⟩ := one_nonvalue (e := .source .return_) rfl eq.symm
        subst actual
        exact ⟨.ret stack, .labelReturn saved ls stack, rfl⟩
      | unreachable => simp [bodyCode, legacyBody, Program.instructions] at member
  | labelTrap =>
    have member : (.trap : Admin) ∈ bodyCode body := by rw [eq]; exact List.Mem.head _
    cases body with
    | trap => exact ⟨.trap, .labelTrap saved ls, rfl⟩
    | code p =>
      cases p with
      | locals code =>
        have check := Locals.limeCodec.supports_encode code
        rw [← body_locals] at check
        exact Bool.noConfusion (check _ member)
      | ret stack =>
        rw [body_return] at member
        have valMember : (.trap : Admin) ∈ values stack := by simpa using member
        exact (value_nonvalue rfl valMember).elim
      | unreachable => simp [bodyCode, legacyBody, Program.instructions] at member
  | otherLabelExit _ _ stack idx tail _ =>
    have member : (.source (.br idx) : Admin) ∈ bodyCode body := by rw [eq]; simp
    cases body with
    | trap => simp [bodyCode, legacyBody] at member
    | code p =>
      cases p with
      | locals code =>
        have check := Locals.limeCodec.supports_encode code
        rw [← body_locals] at check
        exact Bool.noConfusion (check _ member)
      | ret stack =>
        rw [body_return] at member
        exact (value_nonvalue rfl (by simpa using member)).elim
      | unreachable => simp [bodyCode, legacyBody, Program.instructions] at member

private theorem body_step {H : Type} {s s' : Store H} {fn : Callee} {ls : List Value}
    {inner : Frame} {body : Body} {output : List Admin}
    (h : Step limeNoHost ⟨s, fn.frame ls, bodyCode body⟩ ⟨s', inner, output⟩) :
    ∃ ls' next, (∀ saved, Edge fn (.label saved ls body) (.label saved ls' next)) ∧
      (⟨s', inner, output⟩ : Config H) = ⟨s, fn.frame ls', bodyCode next⟩ := by
  cases body with
  | trap =>
    obtain ⟨saved, used, mid, args, head, out⟩ := split h (stack := []) .trap rfl
    obtain ⟨rfl, rfl⟩ := List.nil_eq_append_iff.mp args
    cases head with
    | pure pp => cases pure_focus pp .trap
  | code p =>
    cases p with
    | locals code =>
      have localStep : Step limeNoHost (Locals.limeConfig s fn.module ⟨ls, code⟩) ⟨s', inner, output⟩ := by
        simpa [Locals.limeConfig, Callee.frame] using h
      obtain ⟨out, edge, same⟩ := Locals.lime_step_iff.mp localStep
      exact ⟨out.locals, .code (.locals out.code), fun saved => reduce saved edge, by
        simpa [Locals.limeConfig, Callee.frame] using same⟩
    | ret stack =>
      rw [body_return] at h
      obtain ⟨_, _, _, _, head, _⟩ := split h .ret rfl
      cases head with
      | pure h => cases pure_focus h .ret
    | unreachable =>
      have h' : Step limeNoHost ⟨s, fn.frame ls, [.source .unreachable]⟩ _ := h
      cases singleton_step .unreachable h' with
      | pure h =>
        cases pure_focus h .unreachable
        exact ⟨ls, .trap, fun saved => fact (.unreachable saved ls), rfl⟩

private theorem exit_inner_stuck {H : Type} {s : Store H} {f : Frame} {ready : Exit}
    {dst : Config H} (h : Step limeNoHost ⟨s, f, exitCode ready⟩ dst) : False := by
  cases ready with
  | values stack => exact no_values h
  | ret stack =>
    obtain ⟨_, _, _, _, head, _⟩ := split h .ret (stack := stack) rfl
    cases head with
    | pure h => cases pure_focus h .ret
  | trap =>
    cases singleton_step .trap h with
    | pure pp => cases pure_focus pp .trap

private theorem frame_pop {fn : Callee} {address : FuncAddr} (saved ls : List Value) {ready : Exit} {out : List Admin}
    (h : PureFocus [] (.frame fn.arity (fn.frame ls) (exitCode ready)) out) :
    ∃ q, Ground fn (.exit saved ls ready) q ∧
      values saved ++ out = limeCode address fn q := by
  generalize eq : exitCode ready = code at h
  cases h with
  | frameDone _ _ vs arity =>
    cases ready with
    | values stack =>
      have eq' : values stack = values vs := eq
      have eq'' := value_code_injective eq'
      subst stack
      exact ⟨.returned saved vs, .frameValues saved ls vs arity, by simp [limeCode, legacyCode, values, List.map_append]⟩
    | ret stack => exact (value_nonvalue (e := .source .return_) rfl (by rw [← eq]; simp [exitCode, legacyExit])).elim
    | trap => exact (value_nonvalue (e := .trap) rfl (by rw [← eq]; exact List.Mem.head _)).elim
  | frameReturn _ _ extra vs tail arity =>
    cases ready with
    | values stack => exact (value_nonvalue (stack := stack) (e := .source .return_) rfl
        (by change (.source .return_ : Admin) ∈ exitCode (.values stack); rw [eq]; simp)).elim
    | trap =>
      have mem : (.source .return_ : Admin) ∈ exitCode .trap := by rw [eq]; simp
      simp [exitCode, legacyExit] at mem
    | ret stack =>
      have shape : values (extra ++ vs) ++ [.source .return_] ++ tail =
          values stack ++ [.source .return_] := by simpa [exitCode, legacyExit, values, List.map_append] using eq.symm
      obtain ⟨rfl, _, rfl⟩ := one_nonvalue (e := .source .return_) rfl shape
      exact ⟨.returned saved vs, .frameReturn saved ls extra vs arity, by
        simp [limeCode, legacyCode, values, List.map_append]⟩
  | frameTrap =>
    cases ready with
    | values stack => exact (value_nonvalue (stack := stack) (e := .trap) rfl (by
      change (.trap : Admin) ∈ exitCode (.values stack); rw [eq]; exact List.Mem.head _)).elim
    | ret stack =>
      have mem : (.source .return_ : Admin) ∈ ([.trap] : List Admin) := by rw [← eq]; simp [exitCode, legacyExit]
      simp at mem
    | trap => exact ⟨.trapped saved, .frameTrap saved ls, rfl⟩

private theorem label_inside_frame {n : Nat} {inner : Frame} {body out : List Admin}
    (h : PureFocus [] (.frame n inner [.label n [] body]) out) : False := by
  generalize eq : ([.label n [] body] : List Admin) = code at h
  cases h with
  | frameDone =>
    exact value_nonvalue (e := .label n [] body) rfl (by rw [← eq]; exact List.Mem.head _)
  | frameReturn _ _ extra vs tail arity =>
    have shape : values (extra ++ vs) ++ [.source .return_] ++ tail =
        values [] ++ [.label n [] body] := by simpa [← values_append, values] using eq.symm
    obtain ⟨_, impossible, _⟩ := one_nonvalue (e := .source .return_) rfl shape
    cases impossible
  | frameTrap => cases eq

theorem readback {H : Type} {s : Store H} {caller : Frame} {address : FuncAddr} {fn : Callee}
    (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {dst : Config H} (ready : Admitted fn a)
    (step : Step limeNoHost (limeConfig s caller address fn a) dst) :
    ∃ out, Edge fn a out ∧ dst = limeConfig s caller address fn out := by
  cases a with
  | invoke saved args =>
    obtain ⟨kept, used, mid, stackEq, head, rfl⟩ :=
      split step (stack := saved ++ args) (.invoke address) rfl
    cases head with
    | pure h => cases pure_focus h (.invoke address)
    | wasm found arity =>
      change s.funcs[address.value]? = _ at found
      rw [allocated] at found
      cases found
      have argc : args.length = fn.params.length := by
        simpa using congrArg List.length ready.1
      obtain ⟨rfl, rfl⟩ := returned_suffix stackEq (argc.trans arity.symm)
      exact ⟨.label saved (fn.init args) (.code fn.program), fact (.enter saved args argc), rfl⟩
  | label saved ls body =>
    rcases frame_cases step with ⟨s', inside, code, innerStep, eq⟩ | ⟨rest, pop, _⟩
    · cases singleton_step (.label fn.arity [] (bodyCode body)) innerStep with
      | label bodyStep =>
        let wrap (c : Config H) : Config H := ⟨c.store, caller, values saved ++
          [.frame fn.arity c.frame [.label fn.arity [] c.code]]⟩
        obtain ⟨ls', body', h, same⟩ := body_step bodyStep
        exact ⟨.label saved ls' body', h saved, eq.trans (congrArg wrap same)⟩
      | pure labelStep =>
        obtain ⟨ready, pop, rfl⟩ := label_pop saved ls (pure_focus labelStep (.label fn.arity [] _))
        exact ⟨.exit saved ls ready, fact pop, eq⟩
    · exact (label_inside_frame pop).elim
  | exit saved ls ready =>
    rcases frame_cases step with ⟨_, _, _, h, _⟩ | ⟨out, pop, eq⟩
    · exact (exit_inner_stuck h).elim
    · obtain ⟨q, edge, code⟩ := frame_pop (address := address) saved ls pop
      rw [code] at eq
      exact ⟨q, fact edge, eq⟩
  | returned saved results => exact (no_values step).elim
  | trapped saved =>
    change Step limeNoHost ⟨s, caller, values saved ++ [.trap]⟩ dst at step
    obtain ⟨kept, used, mid, splitStack, head, rfl⟩ := split step .trap rfl
    cases head with
    | pure pp =>
      cases pure_focus pp .trap with
      | bubble v vs =>
        subst saved
        exact ⟨.trapped kept, fact (.bubble kept (v :: vs) (List.cons_ne_nil _ _)), rfl⟩

theorem invoke_wasm_exact {H : Type} {s : Store H} {caller : Frame}
    {i : FuncAddr} {args : List Value} {ty : Wasm.Lime1.FuncType}
    {m : ModuleInst} {fn : Wasm.Lime1.Func} {dst : Config H}
    (allocated : s.funcs[i.value]? = some (.wasm ty m fn)) (count : args.length = ty.params.length) :
    Step CallFrame.limeNoHost ⟨s, caller, values args ++ [.invoke i]⟩ dst ↔
      dst = ⟨s, caller, [.frame ty.results.length ⟨args ++ fn.locals.map Value.zero, m⟩
        [.label ty.results.length [] (expression fn.body)]]⟩ := by
  constructor
  · intro step
    obtain ⟨kept, used, mid, split, head, rfl⟩ :=
      split step (stack := args) (.invoke i) rfl
    cases head with
    | pure pure => cases pure_focus pure (.invoke i)
    | wasm found arity =>
      change s.funcs[i.value]? = _ at found
      rw [allocated] at found
      cases found
      have len := congrArg List.length split
      simp [count, arity] at len
      subst kept
      simp only [List.nil_append] at split
      subst used
      rfl
  · rintro rfl
    exact .invokeWasm s caller i ty m fn args allocated count

end Silmaril.Wasm.Institution.Operational.CallFrame.Proofs.Lime1
