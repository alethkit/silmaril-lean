module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Rules
public import Silmaril.Wasm.Lime1.Execution.Callout
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Lime1Head
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame FuncAddr Value AdminInstr)
open Wasm.Numerics (intBinOp)
open CallContinuation.Proofs.Lime1 (first first_value first_prefix first_head first_values peel wrapper_step frame_label_stays)

private inductive Focus : Wasm.Lime1.Instr → Prop where
  | get (i : LocalIdx) : Focus (.localGet i)
  | bin (t : IntType) (op : IntBinOp) : Focus (.intBinOp t op)
  | call (i : FuncIdx) : Focus (.call i)
  | unreachable : Focus .unreachable

private theorem Focus.nonvalue {op : Wasm.Lime1.Instr} (h : Focus op) :
    asValue? (AdminInstr.source op) = none := by cases h <;> rfl

private inductive Redex (f : Frame) : Wasm.Lime1.Instr → List Value → List Admin → Prop where
  | get {i : LocalIdx} {v : Value} (found : f.locals[i.toNat]? = some v) :
      Redex f (.localGet i) [] [value v]
  | bin {t : IntType} {op : IntBinOp} {x y z : BitVec t.width} (ok : intBinOp t op x y = .ok z) :
      Redex f (.intBinOp t op) [.int t x, .int t y] [value (.int t z)]
  | trap {t : IntType} {op : IntBinOp} {x y : BitVec t.width} {e : Numerics.IntTrap}
      (err : intBinOp t op x y = .error e) :
      Redex f (.intBinOp t op) [.int t x, .int t y] [.trap]
  | call {i : FuncIdx} {a : FuncAddr} (found : f.module.funcs[i.toNat]? = some a) :
      Redex f (.call i) [] [.invoke a]
  | unreachable : Redex f .unreachable [] [.trap]

private theorem redex_shape {stack used : List Value} {op i : Wasm.Lime1.Instr} {rest : List Admin}
    (focus : Focus op) (source : values stack ++ .source op :: rest = values used ++ [.source i])
    (h : asValue? (AdminInstr.source i) = none) : stack = used ∧ op = i ∧ rest = [] := by
  obtain ⟨args, cut, split, hd, tail⟩ := peel (saved := used) (mid := [.source i]) (tail := [])
    ⟨.source i, List.Mem.head _, h⟩ (by simpa using source.symm) focus.nonvalue
  have len := congrArg List.length hd
  simp at len
  have argsNil : args = [] := List.eq_nil_of_length_eq_zero (by omega)
  have cutNil : cut = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst args cut
  exact ⟨by simpa using split, (AdminInstr.source.inj (List.cons.inj hd).1).symm, tail⟩

private theorem read_front {H : Type} {src dst : Config H} (step : Step CallFrame.limeNoHost src dst)
    {stack : List Value} {op : Wasm.Lime1.Instr} {rest : List Admin} (focus : Focus op)
    (source : src.code = values stack ++ .source op :: rest) :
    ∃ saved used next, stack = saved ++ used ∧ Redex src.frame op used next ∧
      dst = ⟨src.store, src.frame, values saved ++ next ++ rest⟩ := by
  have firstEq : first src.code = some (.source op) := by
    rw [source, first_prefix, first_head _ focus.nonvalue]
  induction step generalizing stack rest with
  | @context s s' f f' before after step saved tail ih =>
    obtain ⟨args, cut, rfl, inside, rfl⟩ := peel step.nonvalue source focus.nonvalue
    change before = values args ++ .source op :: cut at inside
    have seen : first before = some (.source op) := by
      rw [inside, first_prefix, first_head _ focus.nonvalue]
    obtain ⟨keep, used, next, rfl, head, eq⟩ := ih inside seen
    refine ⟨saved ++ keep, used, next, List.append_assoc .. |>.symm, head, ?_⟩
    change (⟨s', f', after⟩ : Config H) = _ at eq
    change (⟨s', f', values saved ++ after ++ tail⟩ : Config H) = _
    simpa only [values_append, List.append_assoc] using congrArg (fun c : Config H =>
      (⟨c.store, c.frame, values saved ++ c.code ++ tail⟩ : Config H)) eq
  | localGet s f i v found =>
    obtain ⟨rfl, rfl, rfl⟩ := redex_shape (used := []) focus source.symm rfl
    exact ⟨[], [], _, rfl, .get found, rfl⟩
  | call s f i a found =>
    obtain ⟨rfl, rfl, rfl⟩ := redex_shape (used := []) focus source.symm rfl
    exact ⟨[], [], _, rfl, .call found, rfl⟩
  | pure s f pure =>
    cases pure with
    | intBinary t oper x y z ok =>
      obtain ⟨rfl, rfl, rfl⟩ := redex_shape (used := [.int t x, .int t y]) focus source.symm rfl
      exact ⟨[], _, _, rfl, .bin ok, rfl⟩
    | intBinaryTrap t oper x y e err =>
      obtain ⟨rfl, rfl, rfl⟩ := redex_shape (used := [.int t x, .int t y]) focus source.symm rfl
      exact ⟨[], _, _, rfl, .trap err, rfl⟩
    | unreachable =>
      obtain ⟨rfl, rfl, rfl⟩ := redex_shape (used := []) focus source.symm rfl
      exact ⟨[], [], _, rfl, .unreachable, rfl⟩
    | _ =>
      simp only [List.append_assoc, List.singleton_append, first_prefix, first_value] at firstEq
      first
      | solve
        | simp [first, asValue?] at firstEq
        | simp [first, asValue?] at firstEq
          subst op
          cases focus
  | invokeHost | invokeHostDiverges => contradiction
  | _ =>
    simp only [first_value, first_prefix] at firstEq
    first
    | solve
      | simp [first, asValue?] at firstEq
      | simp [first, asValue?] at firstEq
        subst op
        cases focus

theorem unreachable_iff {H : Type} {s : Store H} {f : Frame}
    {stack : List Value} {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source .unreachable :: rest⟩ dst ↔
      dst = ⟨s, f, values stack ++ .trap :: rest⟩ := by
  constructor
  · intro move
    obtain ⟨saved, _, _, split, head, eq⟩ := read_front move .unreachable rfl
    cases head with
    | unreachable => simpa [split] using eq
  · rintro rfl
    simpa only [List.append_assoc, List.singleton_append] using
      Step.context (Step.pure (host := CallFrame.limeNoHost) s f PureStep.unreachable) stack rest

@[local simp] private theorem values_one (v : Value) : values [v] = [value v] := rfl

@[local simp] private theorem values_two (a b : Value) : values [a, b] = [value a, value b] := rfl

theorem prefix_read {H : Type} {s : Store H} {f : Frame} {stack : List Value} {op : Prefix.Op}
    {suffix : List Admin} {dst : Config H}
    (h : Step CallFrame.limeNoHost ⟨s, f, values stack ++ Prefix.emit limeSyntax op :: suffix⟩ dst) :
    ∃ ans, Prefix.Reduce f.locals stack op ans ∧
      dst = ⟨s, f, Prefix.outcomeCode values .trap suffix ans⟩ := by
  cases op with
  | get i =>
    obtain ⟨saved, used, next, split, head, eq⟩ := read_front h (.get i) rfl
    cases head with
    | get found =>
      have same : stack = saved := by simpa using split
      subst stack
      exact ⟨_, .get found, by simpa [Prefix.outcomeCode, List.append_assoc] using eq⟩
  | bin t op =>
    obtain ⟨saved, used, next, rfl, head, eq⟩ := read_front h (.bin t op) rfl
    cases head with
    | bin ok =>
      exact ⟨_, .bin ok, by simpa [Prefix.outcomeCode, List.append_assoc] using eq⟩
    | trap err => exact ⟨_, .trap err, by simpa [Prefix.outcomeCode] using eq⟩

theorem prefix_sound {H : Type} {s : Store H} {f : Frame} {stack : List Value} {op : Prefix.Op}
    {suffix : List Admin} {ans : Prefix.Outcome} (step : Prefix.Reduce f.locals stack op ans) :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ Prefix.emit limeSyntax op :: suffix⟩
      ⟨s, f, Prefix.outcomeCode values .trap suffix ans⟩ := by
  cases step with
  | get found =>
    simpa [Prefix.outcomeCode, Prefix.emit, limeSyntax, List.append_assoc] using
      Step.context (Step.localGet (host := CallFrame.limeNoHost) s f _ _ found) stack suffix
  | bin ok =>
    simpa [Prefix.outcomeCode, Prefix.emit, limeSyntax, List.append_assoc] using
      Step.context (Step.pure (host := CallFrame.limeNoHost) s f (.intBinary _ _ _ _ _ ok)) _ suffix
  | trap err =>
    simpa [Prefix.outcomeCode, Prefix.emit, limeSyntax, List.append_assoc] using
      Step.context (Step.pure (host := CallFrame.limeNoHost) s f (.intBinaryTrap _ _ _ _ _ err)) _ suffix

theorem prefix_discard_read {A H : Type} {s : Store H} {f : Frame} (emit : A → Admin)
    {stack : List Value} {tail : List A} {dst : Config H}
    (h : Step CallFrame.limeNoHost ⟨s, f, values stack ++ .trap :: tail.map emit⟩ dst) :
    ∃ kept rest, Prefix.Discard stack tail kept rest ∧
      dst = ⟨s, f, values kept ++ .trap :: rest.map emit⟩ := by
  have front := CallContinuation.Proofs.Lime1.front h .trap rfl
  generalize stackEq : stack = vs at front
  generalize tailEq : tail.map emit = tailCode at front
  cases front with
  | normal _ notTrap _ => exact (notTrap rfl).elim
  | bubble kept removed cut rest nz =>
    obtain ⟨left, right, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp tailEq
    subst stack
    exact ⟨kept, right, .cut kept removed left right (by simpa using nz), rfl⟩

theorem prefix_discard_sound {A H : Type} {s : Store H} {f : Frame} (emit : A → Admin)
    {stack kept : List Value} {tail rest : List A} (step : Prefix.Discard stack tail kept rest) :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ .trap :: tail.map emit⟩
      ⟨s, f, values kept ++ .trap :: rest.map emit⟩ := by
  cases step with
  | cut kept removed cut rest nz =>
    cases removed with
    | nil =>
      cases cut with
      | nil => cases nz <;> contradiction
      | cons head cut =>
        simpa [List.append_assoc] using Step.context
          (Step.pure (host := CallFrame.limeNoHost) s f (.trapTail (emit head) (cut.map emit)))
          kept (rest.map emit)
    | cons v vs =>
      simpa [List.append_assoc] using Step.context
        (Step.pure (host := CallFrame.limeNoHost) s f (.trapValues v vs (cut.map emit)))
        kept (rest.map emit)

private theorem read_get {H : Type} {s : Store H} {f : Frame} {stack : List Value} {i : LocalIdx}
    {v : Value} {rest : List Admin} {dst : Config H} (found : f.locals[i.toNat]? = some v)
    (h : Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source (.localGet i) :: rest⟩ dst) :
    dst = ⟨s, f, values stack ++ value v :: rest⟩ := by
  obtain ⟨saved, used, next, split, head, eq⟩ := read_front h (.get i) rfl
  cases head with
  | get lookup =>
    rw [found] at lookup
    cases lookup
    simpa [split] using eq

private theorem read_bin {H : Type} {s : Store H} {f : Frame} {t : IntType} {op : IntBinOp}
    {x y : BitVec t.width} {rest : List Admin} {dst : Config H}
    (h : Step CallFrame.limeNoHost
      ⟨s, f, values [.int t x, .int t y] ++ .source (.intBinOp t op) :: rest⟩ dst) :
    (∃ z, intBinOp t op x y = .ok z ∧ dst = ⟨s, f, value (.int t z) :: rest⟩) ∨
    (∃ e, intBinOp t op x y = .error e ∧ dst = ⟨s, f, .trap :: rest⟩) := by
  obtain ⟨saved, used, next, split, head, eq⟩ := read_front h (.bin t op) rfl
  cases head with
  | bin ok =>
    obtain ⟨rfl, left, right⟩ := two_values split
    cases eq_of_heq (Value.mk.inj left).2
    cases eq_of_heq (Value.mk.inj right).2
    exact .inl ⟨_, ok, eq⟩
  | trap err =>
    obtain ⟨rfl, left, right⟩ := two_values split
    cases eq_of_heq (Value.mk.inj left).2
    cases eq_of_heq (Value.mk.inj right).2
    exact .inr ⟨_, err, eq⟩

theorem read_call {H : Type} {s : Store H} {f : Frame} {stack : List Value} {i : FuncIdx}
    {a : FuncAddr} {rest : List Admin} {dst : Config H} (found : f.module.funcs[i.toNat]? = some a)
    (h : Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source (.call i) :: rest⟩ dst) :
    dst = ⟨s, f, values stack ++ .invoke a :: rest⟩ := by
  obtain ⟨saved, used, next, split, head, eq⟩ := read_front h (.call i) rfl
  cases head with
  | call lookup =>
    rw [found] at lookup
    cases lookup
    simpa [split] using eq

theorem call_iff {H : Type} {s : Store H} {f : Frame}
    {i : FuncIdx} {addr : FuncAddr} {stack : List Value} {tail : List Admin} {dst : Config H}
    (lookup : f.module.funcs[i.toNat]? = some addr) :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source (.call i) :: tail⟩ dst ↔
      dst = ⟨s, f, values stack ++ .invoke addr :: tail⟩ := by
  constructor
  · exact read_call lookup
  · rintro rfl
    simpa only [List.append_assoc, List.singleton_append] using
      Step.context (Step.call (host := CallFrame.limeNoHost) s f i addr lookup) stack tail

theorem label_stays {types : List Wasm.Lime1.FuncType} {n : Nat} {stack : List Value}
    {head : Admin} {rest out : List Admin}
    (none : asValue? head = none) (notBr : ∀ i, head ≠ .source (.br i))
    (notRet : head ≠ .source .return_) (notFinalTrap : head = .trap → stack ≠ [] ∨ rest ≠ [])
    (h : PureStep types [.label n [] (values stack ++ head :: rest)] out) : False := by
  generalize eq : ([.label n [] (values stack ++ head :: rest)] : List Admin) = code at h
  have headEq {body : List Admin} {arity : Nat} {cont : Wasm.Lime1.Expr}
      (e : ([.label n [] (values stack ++ head :: rest)] : List Admin) = [.label arity cont body]) :
      first body = some head :=
    (congrArg first (AdminInstr.label.inj (List.cons.inj e).1).2.2).symm.trans
      (by rw [first_prefix, first_head _ none])
  cases h with
  | labelDone =>
    have seen := headEq eq
    rw [first_values] at seen
    cases seen
  | labelBranch | labelBranchOuter =>
    have seen := headEq eq
    simp only [List.append_assoc, List.singleton_append, first_prefix] at seen
    simp [first, asValue?] at seen
    exact notBr _ seen.symm
  | labelReturn =>
    have seen := headEq eq
    simp only [List.append_assoc, List.singleton_append, first_prefix] at seen
    simp [first, asValue?] at seen
    exact notRet seen.symm
  | labelTrap =>
    have body := (AdminInstr.label.inj (List.cons.inj eq).1).2.2
    have len := congrArg List.length body
    simp only [List.length_append, values_length, List.length_cons, List.length_nil] at len
    have stackNil : stack = [] := List.eq_nil_of_length_eq_zero (by omega)
    have restNil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst stack rest
    cases notFinalTrap (List.cons.inj body).1 <;> contradiction
  | trapValues | trapTail =>
    have len := congrArg List.length eq
    simp [values] at len
  | _ =>
    have last := congrArg List.getLast? eq
    simp [values, List.getLast?_append] at last

theorem lift_body {H : Type} {s s' : Store H} {caller inner inner' : Frame}
    {n : Nat} {a b : List Admin}
    (h : Step CallFrame.limeNoHost ⟨s, inner, a⟩ ⟨s', inner', b⟩) :
    Step CallFrame.limeNoHost ⟨s, caller, [.frame n inner [.label n [] a]]⟩
      ⟨s', caller, [.frame n inner' [.label n [] b]]⟩ :=
  .frame (.label h n []) n caller

theorem body_step_cases {H : Type} {s : Store H} {caller inner : Frame} {n : Nat}
    {body : List Admin} {dst : Config H}
    (h : Step CallFrame.limeNoHost ⟨s, caller, [.frame n inner [.label n [] body]]⟩ dst) :
    (∃ mid : Config H, Step CallFrame.limeNoHost ⟨s, inner, body⟩ mid ∧
      dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] mid.code]]⟩) ∨
    ∃ out, PureStep inner.module.types [.label n [] body] out ∧ dst = ⟨s, caller, [.frame n inner out]⟩ := by
  cases wrapper_step h rfl trivial with
  | pure pop => exact (frame_label_stays pop).elim
  | frame step =>
    cases wrapper_step step rfl trivial with
    | pure pop => exact .inr ⟨_, pop, rfl⟩
    | label innerStep => exact .inl ⟨_, innerStep, rfl⟩

theorem read_body {H : Type} {s : Store H} {caller inner : Frame} {n : Nat}
    {body : List Admin} {dst : Config H}
    (stays : ∀ {out}, PureStep inner.module.types [.label n [] body] out → False)
    (h : Step CallFrame.limeNoHost ⟨s, caller, [.frame n inner [.label n [] body]]⟩ dst) :
    ∃ mid : Config H, Step CallFrame.limeNoHost ⟨s, inner, body⟩ mid ∧
      dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] mid.code]]⟩ := by
  rcases body_step_cases h with body | ⟨_, pop, _⟩
  · exact body
  · exact (stays pop).elim

private theorem trap_step {H : Type} {s : Store H} {f : Frame} {i : FuncIdx} {dst : Config H}
    (h : Step CallFrame.limeNoHost ⟨s, f, [.trap, .source (.call i), .source .nop]⟩ dst) :
    dst = ⟨s, f, [.trap, .source .nop]⟩ ∨ dst = ⟨s, f, [.trap]⟩ := by
  have front := CallContinuation.Proofs.Lime1.front h (vs := []) .trap rfl
  generalize stackEq : ([] : List Value) = stack at front
  generalize tailEq : ([.source (.call i), .source .nop] : List Admin) = tail at front
  cases front with
  | normal _ notTrap _ => exact (notTrap rfl).elim
  | bubble kept removed cut rest nz =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp stackEq.symm
    cases cut with
    | nil => cases nz <;> contradiction
    | cons hd cut =>
      simp at tailEq
      obtain ⟨rfl, tailEq⟩ := tailEq
      cases cut with
      | nil => exact .inl (by rw [List.nil_append] at tailEq; subst rest; rfl)
      | cons hd cut =>
        simp at tailEq
        obtain ⟨rfl, rfl, rfl⟩ := tailEq
        exact .inr rfl

private theorem enter_iff {H : Type} {s : Store H} {caller : Frame} {site : Site} {dst : Config H}
    (g : LimeGuard s caller site) :
    Step CallFrame.limeNoHost (limeConfig s caller site .invoke) dst ↔
      dst = limeConfig s caller site .readLeft := by
  have count : site.args.length = site.type.params.length := by
    simpa [Site.type] using congrArg List.length g.typed.outerArgs
  exact CallFrame.lime_invoke_wasm_exact (caller := caller) g.outerAlloc count

theorem sound {H : Type} {s : Store H} {caller : Frame} {site : Site} {a b : State site}
    (g : LimeGuard s caller site) (edge : Edge site a b) :
    Step CallFrame.limeNoHost (limeConfig s caller site a) (limeConfig s caller site b) := by
  cases invert edge with
  | nest h => exact Nested.lime_sound g.innerAlloc h
  | ground rule =>
    cases rule with
    | resolve => simpa only [limeConfig, limeCode, render, List.append_nil] using
        Step.context (Step.call (host := CallFrame.limeNoHost) s caller _ _ g.outerLookup) site.args []
    | enter => exact (enter_iff g).mpr rfl
    | readLeft =>
      exact lift_body (Step.context (Step.localGet s site.frame _ _ g.typed.leftLookup) [] _)
    | readRight =>
      exact lift_body (Step.context (Step.localGet s site.frame _ _ g.typed.rightLookup) [.int site.kind site.left] _)
    | compute ok => exact lift_body (Step.context (.pure s site.frame (.intBinary _ _ _ _ _ ok)) [] _)
    | trap err => exact lift_body (Step.context (.pure s site.frame (.intBinaryTrap _ _ _ _ _ err)) [] _)
    | dropCall => exact lift_body (Step.context (.pure s site.frame (.trapTail _ [])) [] [.source .nop])
    | dropCallAndNop => exact lift_body (.pure s site.frame (.trapTail _ [.source .nop]))
    | resolveInner z =>
      exact lift_body (Step.context (Step.call s site.frame _ _ g.innerLookup) [.int site.kind z] [.source .nop])

theorem readback {H : Type} {s : Store H} {caller : Frame} {site : Site} {a : State site}
    {dst : Config H} (g : LimeGuard s caller site) (ready : Admitted site a)
    (h : Step CallFrame.limeNoHost (limeConfig s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = limeConfig s caller site out := by
  cases a with
  | call => exact ⟨.invoke, fact .resolve, read_call g.outerLookup h⟩
  | invoke => exact ⟨.readLeft, fact .enter, (enter_iff g).mp h⟩
  | nested q =>
    obtain ⟨out, edge, eq⟩ := (Nested.lime_step_iff g.innerAlloc ready).mp h
    exact ⟨.nested out, delegate edge, eq⟩
  | readLeft =>
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := []) (head := .source (.localGet site.leftIndex)) rfl (by simp) (by simp) (by simp [Site.suffix])) h
    exact ⟨.readRight, fact .readLeft, eq.trans (by rw [read_get g.typed.leftLookup move]; rfl)⟩
  | readRight =>
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := [.int site.kind site.left]) (head := .source (.localGet site.rightIndex))
        rfl (by simp) (by simp) (by simp [Site.suffix])) h
    exact ⟨.compute, fact .readRight, eq.trans (by rw [read_get g.typed.rightLookup move]; rfl)⟩
  | compute =>
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := [.int site.kind site.left, .int site.kind site.right])
        (head := .source (.intBinOp site.kind site.op)) rfl (by simp) (by simp) (by simp [Site.suffix])) h
    rcases read_bin move with ⟨z, ok, rfl⟩ | ⟨_, err, rfl⟩
    · exact ⟨.argument z, fact (.compute ok), eq⟩
    · exact ⟨.argumentTrap, fact (.trap err), eq⟩
  | argument z =>
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := [.int site.kind z]) (head := .source (.call site.innerIndex))
        rfl (by simp) (by simp) (by simp)) h
    exact ⟨.nested (site.innerStart z), fact (.resolveInner z),
      eq.trans (by rw [read_call g.innerLookup move]; rfl)⟩
  | argumentTrap =>
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := []) (head := .trap) rfl (by simp) (by simp) (by simp [Site.suffix])) h
    rcases trap_step move with rfl | rfl
    · exact ⟨_, fact .dropCall, eq⟩
    · exact ⟨_, fact .dropCallAndNop, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Proofs.Lime1
