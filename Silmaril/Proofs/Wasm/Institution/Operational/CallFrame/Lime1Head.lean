module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs
public import Silmaril.Wasm.Lime1.Execution.Callout.Properties
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Sequence

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame.Proofs.Lime1

open Silmaril.Wasm.Lime1.Execution
open Silmaril.Wasm.Execution.Runtime

inductive Focus : Admin → Prop where
  | invoke (a : FuncAddr) : Focus (.invoke a)
  | frame (n : Nat) (f : Frame) (body : List Admin) : Focus (.frame n f body)
  | label (n : Nat) (cont : List Wasm.Lime1.Instr) (body : List Admin) : Focus (.label n cont body)
  | unreachable : Focus (.source .unreachable)
  | ret : Focus (.source .return_)
  | trap : Focus .trap

inductive PureFocus : List Value → Admin → List Admin → Prop where
  | unreachable : PureFocus [] (.source .unreachable) [.trap]
  | bubble (v : Value) (vs : List Value) : PureFocus (v :: vs) .trap [.trap]
  | labelDone (n : Nat) (cont : List Wasm.Lime1.Instr) (vs : List Value) :
      PureFocus [] (.label n cont (values vs)) (values vs)
  | labelReturn (n : Nat) (cont : List Wasm.Lime1.Instr) (vs : List Value) (tail : List Admin) :
      PureFocus [] (.label n cont (values vs ++ [.source .return_] ++ tail))
        (values vs ++ [.source .return_])
  | labelTrap (n : Nat) (cont : List Wasm.Lime1.Instr) :
      PureFocus [] (.label n cont [.trap]) [.trap]
  | frameDone (n : Nat) (f : Frame) (vs : List Value) (arity : vs.length = n) :
      PureFocus [] (.frame n f (values vs)) (values vs)
  | frameReturn (n : Nat) (f : Frame) (extra vs : List Value) (tail : List Admin) (arity : vs.length = n) :
      PureFocus [] (.frame n f (values extra ++ values vs ++ [.source .return_] ++ tail)) (values vs)
  | frameTrap (n : Nat) (f : Frame) : PureFocus [] (.frame n f [.trap]) [.trap]
  | otherLabelExit (n : Nat) (cont : List Wasm.Lime1.Instr) (vs : List Value)
      (idx : LabelIdx) (tail : List Admin) (out : List Admin) :
      PureFocus [] (.label n cont (values vs ++ [.source (.br idx)] ++ tail)) out

private theorem single {top op : Admin} {args : List Value} (eq : [top] = values args ++ [op]) :
    args = [] ∧ top = op := by
  have len := congrArg List.length eq
  simp at len
  subst args
  exact ⟨rfl, List.cons.inj eq |>.1⟩

theorem pure_focus {types : List Wasm.Lime1.FuncType} {args : List Value} {op : Admin} {out : List Admin}
    (h : PureStep types (values args ++ [op]) out) (focus : Focus op) :
    PureFocus args op out := by
  generalize eq : values args ++ [op] = before at h
  cases h with
  | unreachable =>
    obtain ⟨rfl, rfl⟩ := single eq.symm
    exact .unreachable
  | labelDone n cont vs =>
    obtain ⟨rfl, rfl⟩ := single eq.symm
    exact .labelDone n cont vs
  | labelReturn n cont vs tail =>
    obtain ⟨rfl, rfl⟩ := single eq.symm
    exact .labelReturn n cont vs tail
  | labelTrap n cont =>
    obtain ⟨rfl, rfl⟩ := single eq.symm
    exact .labelTrap n cont
  | frameDone n fr vs arity =>
    obtain ⟨rfl, rfl⟩ := single eq.symm
    exact .frameDone n fr vs arity
  | frameReturn n fr extra vs tail arity =>
    obtain ⟨rfl, rfl⟩ := single eq.symm
    exact .frameReturn n fr extra vs tail arity
  | frameTrap n fr =>
    obtain ⟨rfl, rfl⟩ := single eq.symm
    exact .frameTrap n fr
  | labelBranch n cont extra vs tail arity =>
    obtain ⟨rfl, rfl⟩ := single eq.symm
    simpa only [← values_append] using
      PureFocus.otherLabelExit n cont (extra ++ vs) ⟨0⟩ tail (values vs ++ expression cont)
  | labelBranchOuter n cont vs tail idx bound =>
    obtain ⟨rfl, rfl⟩ := single eq.symm
    exact .otherLabelExit n cont vs idx tail _
  | trapValues v vs tail =>
    obtain ⟨more, same, one, rfl⟩ := split_context value asValue? asValue?_value (v :: vs) args
      (mid := [.trap]) (tail := tail) ⟨.trap, List.Mem.head _, rfl⟩ eq.symm
    obtain ⟨rfl, rfl⟩ := single one
    rw [same, List.append_nil]
    exact .bubble v vs
  | trapTail hd tail =>
    obtain ⟨_, _, _, impossible⟩ := split_context value asValue? asValue?_value [] args
      (mid := [.trap]) (tail := hd :: tail) ⟨.trap, List.Mem.head _, rfl⟩ eq.symm
    cases impossible
  | _ =>
    have last := congrArg List.getLast? eq
    simp [values] at last
    subst op
    cases focus

private theorem pure_active {types : List Wasm.Lime1.FuncType} {a b : List Admin} (h : PureStep types a b) :
    ∃ x ∈ a, asValue? x = none := by
  cases h with
  | trapValues v vs tail => exact ⟨.trap, by simp, rfl⟩
  | block bt code ft found vs arity => exact ⟨.source (.block bt code), by simp, rfl⟩
  | loop bt code ft found vs arity => exact ⟨.source (.loop bt code), by simp, rfl⟩
  | _ =>
    by_contra absent
    push Not at absent
    simp [asValue?, values] at absent

private theorem active {H : Type} {host : HostSemantics H} {a b : Config H} (h : Step host a b) :
    ∃ x ∈ a.code, asValue? x = none := by
  induction h with
  | pure _ _ h => exact pure_active h
  | context _ saved tail ih =>
    obtain ⟨x, mem, hv⟩ := ih
    exact ⟨x, by simp [mem], hv⟩
  | invokeWasm s f a ft m fn args found arity  =>
    exact ⟨.invoke a, by simp, rfl⟩
  | invokeHost s s' f a ft fn args r found arity behavior =>
    exact ⟨.invoke a, by simp, rfl⟩
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    exact ⟨.invoke a, by simp, rfl⟩
  | _ =>
    by_contra absent
    push Not at absent
    simp [asValue?] at absent

inductive HeadStep {H : Type} (s : Store H) (f : Frame) : List Value → Admin → Config H → Prop where
  | pure {args op out} (h : PureStep f.module.types (values args ++ [op]) out) :
      HeadStep s f args op ⟨s, f, out⟩
  | label {n cont body s' f' out}
      (step : Step limeNoHost ⟨s, f, body⟩ ⟨s', f', out⟩) :
      HeadStep s f [] (.label n cont body) ⟨s', f', [.label n cont out]⟩
  | frame {n inner body s' inner' out}
      (step : Step limeNoHost ⟨s, inner, body⟩ ⟨s', inner', out⟩) :
      HeadStep s f [] (.frame n inner body) ⟨s', f, [.frame n inner' out]⟩
  | wasm {a ft module fn args} (found : s.funcs[a.value]? = some (.wasm ft module fn))
      (arity : args.length = ft.params.length) :
      HeadStep s f args (.invoke a)
        ⟨s, f, [.frame ft.results.length ⟨args ++ fn.locals.map Value.zero, module⟩
          [.label ft.results.length [] (expression fn.body)]]⟩

theorem split {H : Type} {src dst : Config H} (step : Step limeNoHost src dst) {stack : List Value}
    {op : Admin} (focus : Focus op) (source : src.code = values stack ++ [op]) :
    ∃ kept args middle, stack = kept ++ args ∧ HeadStep src.store src.frame args op middle ∧
      dst = ⟨middle.store, middle.frame, values kept ++ middle.code⟩ := by
  induction step generalizing stack with
  | pure s f step =>
    exact ⟨[], stack, _, rfl, .pure (source ▸ step), rfl⟩
  | @context s s' f f' before after step saved tail ih =>
    obtain ⟨args, rfl, inner, rfl⟩ :=
      split_context value asValue? asValue?_value saved stack (active step) source
    obtain ⟨kept, used, middle, rfl, redex, out⟩ := ih inner
    exact ⟨saved ++ kept, used, middle, by simp [List.append_assoc], redex, by
      change (⟨s', f', values saved ++ after ++ []⟩ : Config H) = _
      change (⟨s', f', after⟩ : Config H) = _ at out
      simpa [values, List.map_append, List.append_assoc] using
        congrArg (fun c : Config H => (⟨c.store, c.frame, values saved ++ c.code⟩ : Config H)) out⟩
  | @label s s' f f' before after h n cont _ =>
    have len := congrArg List.length source
    simp at len
    subst stack
    have eq : AdminInstr.label n cont before = op := by simpa [values] using source
    subst op
    exact ⟨[], [], _, rfl, .label h, rfl⟩
  | @frame s s' inner inner' before after h n outer _ =>
    have len := congrArg List.length source
    simp at len
    subst stack
    have eq : AdminInstr.frame n inner before = op := by simpa [values] using source
    subst op
    exact ⟨[], [], _, rfl, .frame h, rfl⟩
  | invokeWasm s f a ft module fn args found arity  =>
    have eq : AdminInstr.invoke a = op := by
      simpa using congrArg List.getLast? source
    subst op
    have sameStack : args = stack := stack_injective value asValue? asValue?_value
      (List.append_cancel_right source)
    subst stack
    exact ⟨[], args, _, rfl, .wasm found arity, rfl⟩
  | invokeHost => contradiction
  | invokeHostDiverges => contradiction
  | _ =>
    have eq := congrArg List.getLast? source
    simp [values] at eq
    subst op
    cases focus

theorem no_values {H : Type} {s : Store H} {f : Frame} {stack : List Value} {dst : Config H}
    (step : Step limeNoHost ⟨s, f, values stack⟩ dst) : False := by
  obtain ⟨x, h, hx⟩ := active step
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp h
  simp at hx

end Silmaril.Wasm.Institution.Operational.CallFrame.Proofs.Lime1
