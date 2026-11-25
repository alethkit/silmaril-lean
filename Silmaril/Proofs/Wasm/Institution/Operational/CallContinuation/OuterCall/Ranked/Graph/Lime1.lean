module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Context
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.NativeCommon
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Rules
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms

import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution
open Execution.Runtime (Frame FuncAddr Value)
open Computed

private abbrev native {H : Type} := Step (H := H) CallFrame.limeNoHost

private theorem code_expression (code : List Op) :
    expression (Op.emitList limeCodeSyntax code) = code.map limeAdmin.emit := by
  induction code with
  | nil => rfl
  | cons op rest ih =>
    change _ :: expression (Op.emitList limeCodeSyntax rest) = _ :: rest.map limeAdmin.emit
    rw [ih]
    cases op with
    | numeric op => cases op <;> rfl
    | set | tee | call | block | if_ | br | return_ | unreachable => rfl

private theorem expression_code (fn : Function) :
    expression fn.limeFunc.body = (Body.running fn.initial fn.code).render limeAdmin := by
  change expression (fn.initial.map Sequence.limeSource.value ++ Op.emitList limeCodeSyntax fn.code) =
    values fn.initial ++ fn.code.map limeAdmin.emit
  rw [show expression (fn.initial.map Sequence.limeSource.value ++ Op.emitList limeCodeSyntax fn.code) =
      expression (fn.initial.map Sequence.limeSource.value) ++ expression (Op.emitList limeCodeSyntax fn.code) from
    List.map_append .., code_expression]
  congr 1
  change (fn.initial.map Sequence.limeSource.value).map _ = _
  simp only [List.map_map, values]
  apply List.map_congr_left
  intro v _
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

private def limeAt {H : Type} (s : Store H) (caller : Frame) (target : CallTarget) (n : Nat) (q : Phase) : Config H :=
  ⟨s, caller, q.renderAt limeAdmin target n⟩

private theorem attach_code (saved : List Value) (target : CallTarget) (rest : List Op) (q : Phase) :
    (Body.attach saved target rest q).render limeAdmin =
      values saved ++ q.render limeAdmin target ++ rest.map limeAdmin.emit :=
  render_attach values_append saved target rest q

private theorem lift_label {H : Type} {s : Store H} {caller parent parentNext : Frame} {n : Nat}
    {before after : List Admin} (move : native ⟨s, parent, before⟩ ⟨s, parentNext, after⟩) :
    native ⟨s, caller, [.frame n parent [.label n [] before]]⟩
      ⟨s, caller, [.frame n parentNext [.label n [] after]]⟩ :=
  .frame (.label move n []) n caller

private theorem set_sound {H : Type} {s : Store H} {decl : Declaration}
    {locals next saved : List Value} {v : Value} {idx : LocalIdx} {rest : List Op}
    (write : Locals.Edge ⟨locals, [.value v, .set idx]⟩ ⟨next, []⟩) :
    Step CallFrame.limeNoHost ⟨s, currentFrame decl locals, (Body.running (saved ++ [v]) (.set idx :: rest)).render limeAdmin⟩
      ⟨s, currentFrame decl next, (Body.running saved rest).render limeAdmin⟩ := by
  have move := Locals.lime_sound (host := CallFrame.limeNoHost) (s := s) (m := decl.module) write
  have lifted := Step.context move saved (rest.map limeAdmin.emit)
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Locals.Codec.encode, Locals.limeCodec, Locals.legacyCodec,
    Locals.limeInstr, currentFrame, Body.render, limeAdmin, limeEmit, Op.emit, limeCodeSyntax,
    List.append_assoc, values] at lifted ⊢ <;> exact lifted

private theorem tee_sound {H : Type} {s : Store H} {decl : Declaration}
    {locals saved : List Value} {v : Value} {idx : LocalIdx} {rest : List Op}
    (write : Locals.Edge ⟨locals, [.value v, .tee idx]⟩ ⟨locals, [.value v, .value v, .set idx]⟩) :
    Step CallFrame.limeNoHost ⟨s, currentFrame decl locals, (Body.running (saved ++ [v]) (.tee idx :: rest)).render limeAdmin⟩
      ⟨s, currentFrame decl locals, (Body.running (saved ++ [v, v]) (.set idx :: rest)).render limeAdmin⟩ := by
  have move := Locals.lime_sound (host := CallFrame.limeNoHost) (s := s) (m := decl.module) write
  have lifted := Step.context move saved (rest.map limeAdmin.emit)
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Locals.Codec.encode, Locals.limeCodec, Locals.legacyCodec,
    Locals.limeInstr, currentFrame, Body.render, limeAdmin, limeEmit, Op.emit, limeCodeSyntax,
    List.append_assoc, values] at lifted ⊢ <;> exact lifted

private theorem entry_iff {H : Type} {s : Store H} {caller : Frame} {fn : Function} {target : CallTarget}
    {saved args : List Value} {rest : List Admin} {dst : Config H}
    (declared : fn.declaration = target.declaration)
    (alloc : s.funcs[target.address.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.limeFunc))
    (typed : args.map Value.type = fn.declaration.params) :
    native ⟨s, caller, values (saved ++ args) ++ .invoke target.address :: rest⟩ dst ↔
      dst = ⟨s, caller, values saved ++
        (Phase.label (fn.declaration.frame args).locals (.running fn.initial fn.code)).render limeAdmin target ++ rest⟩ := by
  have count : args.length = fn.declaration.type.params.length :=
    (List.length_map ..).symm.trans (congrArg List.length typed)
  have entry (out : Config H) :=
    CallFrame.lime_invoke_wasm_prefix_iff (caller := caller) (saved := saved) (dst := out) alloc count
  have entered : [.frame fn.declaration.type.results.length
      ⟨args ++ fn.limeFunc.locals.map Value.zero, fn.declaration.module⟩
      [.label fn.declaration.type.results.length [] (expression fn.limeFunc.body)]] =
      (Phase.label (fn.declaration.frame args).locals (.running fn.initial fn.code)).render limeAdmin target := by
    rw [expression_code, Phase.render, Phase.renderAt, ← declared]
    rfl
  constructor
  · intro move
    obtain ⟨mid, step, eq⟩ := CallContinuation.lime_invoke_strip_suffix move
    obtain rfl := (entry mid).mp step
    simpa only [← entered, List.append_assoc] using eq
  · rintro rfl
    have step := (entry _).mpr rfl
    simpa only [← entered, values, List.map_nil, List.nil_append, List.append_assoc, List.singleton_append] using
      Step.context step [] rest

private theorem running_stays {types : List Wasm.Lime1.FuncType} {n : Nat} {v : List Value} {op : Op}
    {rest : List Op} {out : List Admin}
    (notBranch : ∀ depth result, op ≠ .br depth result) (notReturn : op ≠ .return_)
    (pop : PureStep types [.label n [] ((Body.running v (op :: rest)).render limeAdmin)] out) : False := by
  change PureStep types [.label n [] (values v ++ limeAdmin.emit op :: rest.map limeAdmin.emit)] out at pop
  cases op with
  | numeric p =>
    cases p <;> exact Computed.lime_label_stays (head := limeAdmin.emit (.numeric _)) (by rfl)
      (by simp [limeAdmin, limeEmit, Prefix.emit, limeSyntax])
      (by simp [limeAdmin, limeEmit, Prefix.emit, limeSyntax])
      (by simp [limeAdmin, limeEmit, Prefix.emit, limeSyntax]) pop
  | set idx =>
    exact Computed.lime_label_stays (head := .source (.localSet idx)) rfl (by simp) (by simp) (by simp) pop
  | tee idx =>
    exact Computed.lime_label_stays (head := .source (.localTee idx)) rfl (by simp) (by simp) (by simp) pop
  | call t => exact Computed.lime_label_stays (head := .source (.call t.index)) rfl (by simp) (by simp) (by simp) pop
  | if_ result thenBody elseBody =>
    exact Computed.lime_label_stays (head := limeAdmin.emit (.if_ result thenBody elseBody)) rfl
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax]) pop
  | block result body =>
    exact Computed.lime_label_stays (head := limeAdmin.emit (.block result body)) rfl
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax]) pop
  | br depth result => exact notBranch depth result rfl
  | return_ => exact notReturn rfl
  | unreachable => exact Computed.lime_label_stays (head := .source .unreachable) rfl (by simp) (by simp) (by simp) pop

private theorem active_entered_iff {H : Type} {s : Store H} {program : Program} (checked : program.check = true) (n : Nat)
    {caller : Frame} {root target : CallTarget} {fn : Function}
    (found : program.lookup root.address = some fn) (used : target ∈ fn.targets)
    {locals saved : List Value} {rest : List Op} {child : Phase} (live : child.Active)
    {k : Nat} {f : Frame} {code : List Admin} (rendered : child.render limeAdmin target = [.frame k f code])
    (childStep : ∀ {dst}, native (limeConfig s (currentFrame root.declaration locals) target child) dst ↔
      ∃ out, program.Edge checked target.address child out ∧ dst = limeConfig s (currentFrame root.declaration locals) target out)
    {dst : Config H} :
    native (limeAt s caller root n (.label locals (.active saved target child rest))) dst ↔
      ∃ out, program.Edge checked root.address (.label locals (.active saved target child rest)) out ∧
        dst = limeAt s caller root n out := by
  have ctx : native (limeAt s caller root n (.label locals (.active saved target child rest))) dst ↔
      ∃ mid, native (limeConfig s (currentFrame root.declaration locals) target child) mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame
          [.label n [] (values saved ++ mid.code ++ rest.map limeAdmin.emit)]]⟩ := by
    change native ⟨s, caller, [.frame n (currentFrame root.declaration locals)
        [.label n [] (values saved ++ child.render limeAdmin target ++ rest.map limeAdmin.emit)]]⟩ dst ↔
      ∃ mid, native ⟨s, currentFrame root.declaration locals, child.render limeAdmin target⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame
          [.label n [] (values saved ++ mid.code ++ rest.map limeAdmin.emit)]]⟩
    rw [rendered, List.append_assoc, List.singleton_append]
    exact lime_entered_child_iff
  rw [ctx]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, childEdge, rfl⟩ := childStep.mp move
    refine ⟨.label locals (Body.attach saved target rest out),
      (program.active_iff checked found used live).mpr ⟨out, childEdge, rfl⟩, ?_⟩
    change _ = (⟨s, caller, [.frame _ _ [.label _ [] ((Body.attach saved target rest out).render limeAdmin)]]⟩ : Config H)
    rw [attach_code]
    rfl
  · rintro ⟨out, move, rfl⟩
    obtain ⟨childOut, childEdge, rfl⟩ := (program.active_iff checked found used live).mp move
    refine ⟨_, childStep.mpr ⟨childOut, childEdge, rfl⟩, ?_⟩
    change (⟨s, caller, [.frame _ _ [.label _ [] ((Body.attach saved target rest childOut).render limeAdmin)]]⟩ : Config H) = _
    rw [attach_code]
    rfl

private theorem under_label_iff {H : Type} {s : Store H} {caller parent : Frame} {n : Nat}
    {code : List Admin} {dst : Config H}
    (stays : ∀ {out}, PureStep parent.module.types [.label n [] code] out → False) :
    native ⟨s, caller, [.frame n parent [.label n [] code]]⟩ dst ↔
      ∃ mid : Config H, native ⟨s, parent, code⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] mid.code]]⟩ := by
  constructor
  · intro move
    rcases Computed.lime_body_step_cases move with inside | ⟨_, pop, _⟩
    · exact inside
    · exact (stays pop).elim
  · rintro ⟨⟨_, _, _⟩, move, rfl⟩
    exact .frame (.label move n []) n caller

private theorem pending_child_iff {H : Type} {s : Store H} {program : Program} (checked : program.check = true) (n : Nat)
    (allocated : program.LimeAllocated s) {caller : Frame} {root target : CallTarget} {fn callee : Function}
    (found : program.lookup root.address = some fn) (used : target ∈ fn.targets)
    (childFound : program.lookup target.address = some callee) (declared : callee.declaration = target.declaration)
    {locals saved operands : List Value} {rest : List Op} (typed : operands.map Value.type = callee.declaration.params)
    {dst : Config H} :
    native (limeAt s caller root n (.label locals (.active saved target (.invoke operands) rest))) dst ↔
      ∃ out, program.Edge checked root.address (.label locals (.active saved target (.invoke operands) rest)) out ∧
        dst = limeAt s caller root n out := by
  have stays {out : List Admin} (pop : PureStep (currentFrame root.declaration locals).module.types
      [.label n []
        (values (saved ++ operands) ++ .invoke target.address :: rest.map limeAdmin.emit)] out) : False :=
    Computed.lime_label_stays (head := .invoke target.address) rfl (by simp) (by simp) (by simp) pop
  have ctx := under_label_iff (s := s) (caller := caller) (dst := dst) stays
  have entry {mid : Config H} := entry_iff (caller := currentFrame root.declaration locals) (saved := saved)
    (rest := rest.map limeAdmin.emit) (dst := mid) declared (allocated _ _ childFound) typed
  have live : (Phase.invoke operands).Active := trivial
  have source : (Body.active saved target (.invoke operands) rest).render limeAdmin =
      values (saved ++ operands) ++ .invoke target.address :: rest.map limeAdmin.emit := by
    change values saved ++ (values operands ++ [.invoke target.address]) ++ rest.map limeAdmin.emit = _
    rw [values_append]
    simp only [List.append_assoc, List.singleton_append]
  change native ⟨s, caller, [.frame _ _ [.label _ [] ((Body.active saved target (.invoke operands) rest).render limeAdmin)]]⟩ dst ↔ _
  rw [source, ctx]
  constructor
  · rintro ⟨mid, move, eq⟩
    obtain rfl := entry.mp move
    refine ⟨_, (program.active_iff checked found used live).mpr
      ⟨_, (program.edge_iff checked childFound).mpr (.enter operands typed), rfl⟩, ?_⟩
    exact eq
  · rintro ⟨out, edge, rfl⟩
    obtain ⟨childOut, step, rfl⟩ := (program.active_iff checked found used live).mp edge
    cases (program.edge_iff checked childFound).mp step with
    | enter _ _ => exact ⟨_, entry.mpr rfl, rfl⟩

private theorem trapped_not_final {n : Nat} {stack : List Value} {rest : List Op} {types : List Wasm.Lime1.FuncType}
    {out : List Admin} (pop : PureStep types [.label n [] ((Body.trapped stack rest).render limeAdmin)] out) :
    stack = [] ∧ rest = [] := by
  by_contra unfinished
  exact Computed.lime_label_stays (head := .trap) rfl (by simp) (by simp)
    (fun _ => by simpa using not_and_or.mp unfinished) pop

private theorem sequence_label_iff {H : Type} {s : Store H} {f : Frame} {n : Nat}
    {saved : List Value} {body rest : List Admin} {dst : Config H} :
    native ⟨s, f, values saved ++ .label n [] body :: rest⟩ dst ↔
      ∃ mid, native ⟨s, f, [.label n [] body]⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ mid.code ++ rest⟩ := by
  constructor
  · intro move
    rcases Blocks.Context.lime_label_iff.mp move with ⟨mid, inside, rfl⟩ | ⟨out, pop, rfl⟩
    · exact ⟨_, .label inside n [], by simp only [List.append_assoc, List.singleton_append]⟩
    · exact ⟨_, .pure s f pop, rfl⟩
  · rintro ⟨⟨_, _, _⟩, move, rfl⟩
    simpa only [List.append_assoc, List.singleton_append] using Step.context move saved rest

private def inFrame {H : Type} (outer : Frame) (n : Nat) (q : Config H) : Config H :=
  ⟨q.store, outer, [.frame n q.frame q.code]⟩

private theorem inFrame_injective {H : Type} (outer : Frame) (n : Nat) :
    Function.Injective (inFrame (H := H) outer n) := by
  intro a b eq
  cases a
  cases b
  simp_all [inFrame]

private theorem label_frame_iff {H : Type} {s : Store H} {outer inner : Frame}
    {n : Nat} {body : List Admin} {dst : Config H} :
    native (inFrame outer n ⟨s, inner, [.label n [] body]⟩) dst ↔
      ∃ mid, native ⟨s, inner, [.label n [] body]⟩ mid ∧ dst = inFrame outer n mid := by
  constructor
  · intro move
    rcases Computed.lime_body_step_cases move with ⟨mid, inside, rfl⟩ | ⟨out, pop, rfl⟩
    · exact ⟨_, .label inside n [], rfl⟩
    · exact ⟨_, .pure s inner pop, rfl⟩
  · rintro ⟨⟨_, _, _⟩, move, rfl⟩
    exact .frame move n outer

private theorem branch_step_iff {H : Type} {s : Store H} {program : Program}
    (checked : program.check = true) {caller : Frame} {target : CallTarget} {fn : Function}
    (found : program.lookup target.address = some fn) {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {locals stack : List Value} {depth : LabelIdx} {result : Option NumType} {rest : List Op}
    (typed : fn.WellTyped stack (.br depth result :: rest) fallthrough enclosing) {dst : Config H} :
    native (limeAt s caller target fallthrough.length (.label locals (.running stack (.br depth result :: rest)))) dst ↔
      ∃ out, program.Edge checked target.address (.label locals (.running stack (.br depth result :: rest))) out ∧
        dst = limeAt s caller target fallthrough.length out := by
  let n := fallthrough.length
  change native (inFrame caller n
    ⟨s, currentFrame target.declaration locals, [.label n [] (values stack ++ .source (.br depth) :: rest.map limeAdmin.emit)]⟩) dst ↔ _
  rw [label_frame_iff]
  have rule {a b : Phase} := program.edge_iff checked (a := a) (b := b) found
  have invert {mid : Config H} := BranchExit.lime_label_br_iff  (s := s)
    (host := CallFrame.limeNoHost) (f := currentFrame target.declaration locals) (stack := stack)
    (n := fallthrough.length) (depth := depth) (rest := rest.map limeAdmin.emit) (dst := mid)
  constructor
  · rintro ⟨mid, move, rfl⟩
    rcases invert.mp move with ⟨extra, payload, split, size, here, rfl⟩ | ⟨outer, rfl⟩
    · subst stack
      obtain rfl : depth = ⟨0⟩ := Idx.toNat_injective here
      have arity := size.trans (congrArg List.length (branch_here_result (checked_branch typed).1))
      exact ⟨_, rule.mpr (.branchHere locals extra payload result rest arity), rfl⟩
    · exact ⟨_, rule.mpr (.branchOuter locals stack depth result rest outer), rfl⟩
  · rintro ⟨out, edge, rfl⟩
    cases rule.mp edge with
    | branchHere _ extra payload _ _ arity =>
      have size : (payload).length = fallthrough.length := arity.trans (congrArg List.length (branch_here_result (checked_branch typed).1)).symm
      exact ⟨_, invert.mpr (.inl ⟨extra, payload, rfl, size, rfl, rfl⟩), rfl⟩
    | branchOuter _ _ _ _ _ outer =>
      exact ⟨_, invert.mpr (.inr ⟨outer, rfl⟩), rfl⟩

private theorem block_step_iff {H : Type} {s : Store H} {program : Program}
    (checked : program.check = true) {caller : Frame} {target : CallTarget} {fn : Function}
    (found : program.lookup target.address = some fn) {n : Nat} {locals saved : List Value} {result : Option NumType}
    {inner : Body} {rest : List Op}
    (inside : ∀ {dst}, native (limeAt s caller target result.toList.length (.label locals inner)) dst ↔
      ∃ next, program.Edge checked target.address (.label locals inner) next ∧
        dst = limeAt s caller target result.toList.length next)
    {dst : Config H} :
    native (limeAt s caller target n (.label locals (.block saved result inner rest))) dst ↔
      ∃ out, program.Edge checked target.address (.label locals (.block saved result inner rest)) out ∧
        dst = limeAt s caller target n out := by
  let k := result.toList.length
  let code := values saved ++ (.label k [] (inner.render limeAdmin) : Admin) :: rest.map limeAdmin.emit
  have stays {out} (pop : PureStep (currentFrame target.declaration locals).module.types [.label n [] code] out) : False := by
    exact Computed.lime_label_stays (head := .label k [] (inner.render limeAdmin)) rfl
      (by simp) (by simp) (by simp) pop
  change native ⟨s, caller, [.frame n (currentFrame target.declaration locals) [.label n [] code]]⟩ dst ↔ _
  rw [under_label_iff stays]
  have render {next} (edge : program.Edge checked target.address (.label locals inner) next) :=
    render_block limeAdmin values_append rfl target n saved result rest next
      (label_outcome ((edge_iff checked found).mp edge) ⟨_, _, rfl⟩)
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨branch, step, rfl⟩ := (sequence_label_iff (saved := saved)).mp move
    have lifted : native (limeAt s caller target k (.label locals inner)) (inFrame caller k branch) := .frame step k caller
    obtain ⟨next, edge, eq⟩ := inside.mp lifted
    obtain ⟨ls, code, before, after⟩ := render edge
    have related : inFrame caller k (⟨s, (currentFrame target.declaration ls), code⟩ : Config H) =
        limeAt s caller target k next := by rw [limeAt, before]; rfl
    have same := inFrame_injective caller k (eq.trans related.symm)
    subst branch
    exact ⟨_, (block_iff checked found).mpr ⟨next, edge, rfl⟩, by rw [limeAt, after]; rfl⟩
  · rintro ⟨out, edge, rfl⟩
    obtain ⟨next, move, rfl⟩ := (block_iff checked found).mp edge
    have lifted := inside.mpr ⟨next, move, rfl⟩
    obtain ⟨branch, step, eq⟩ := label_frame_iff.mp lifted
    obtain ⟨ls, code, before, after⟩ := render move
    have related : limeAt s caller target k next =
        inFrame caller k (⟨s, (currentFrame target.declaration ls), code⟩ : Config H) := by
      rw [limeAt, before]; rfl
    have same := inFrame_injective caller k (eq.symm.trans related)
    subst branch
    refine ⟨_, (sequence_label_iff (saved := saved)).mpr ⟨_, step, rfl⟩, ?_⟩
    rw [limeAt, after]
    rfl

private theorem region_step_iff {H : Type} {s : Store H} {program : Program} (checked : program.check = true)
    (allocated : program.LimeAllocated s) {caller : Frame} {target : CallTarget} {fn : Function}
    (root : Root program caller target fn)
    (descend : ∀ child ∈ fn.targets, ∀ {parent callee q dst},
      Root program parent child callee → Admitted program callee q →
      (native (limeConfig s parent child q) dst ↔
        ∃ out, program.Edge checked child.address q out ∧ dst = limeConfig s parent child out))
    (size : Nat) : ∀ {body locals fallthrough enclosing dst}, sizeOf body = size →
      AdmittedAt program fn fallthrough enclosing (.label locals body) →
      (native (limeAt s caller target fallthrough.length (.label locals body)) dst ↔
        ∃ out, program.Edge checked target.address (.label locals body) out ∧
          dst = limeAt s caller target fallthrough.length out) := by
  induction size using Nat.strong_induction_on with
  | ind size ih =>
    intro body locals fallthrough enclosing dst sizeEq ready
    let n := fallthrough.length
    have rule {a b : Phase} := program.edge_iff checked (a := a) (b := b) root.found
    cases ready with
    | @running _ _ _ locals stack rest typed codeTyped =>
      cases rest with
      | nil =>
        constructor
        · intro move
          rcases Computed.lime_body_step_cases move with ⟨_, inside, _⟩ | ⟨_, pop, eq⟩
          · exact (Nested.lime_result_stuck (r := .values stack) (by simpa only [Body.render, limeAdmin,
              List.map_nil, List.append_nil, Nested.resultCode] using inside)).elim
          · exact ⟨_, rule.mpr (.leaveValues locals stack), eq.trans (by
              have leave := Nested.lime_label_result (r := .values stack)
                (by simpa only [Body.render, limeAdmin, List.map_nil, List.append_nil, Nested.resultCode] using pop)
              rw [leave]
              rfl)⟩
        · rintro ⟨out, move, rfl⟩
          cases rule.mp move with
          | leaveValues =>
            simpa only [limeAt, Phase.renderAt, Body.render, limeAdmin, List.map_nil, List.append_nil, Nested.resultCode] using
              Step.frame (Step.pure (host := CallFrame.limeNoHost) s (currentFrame target.declaration locals)
                (.labelDone n [] stack)) n caller
      | cons op rest =>
        by_cases isBranch : ∃ depth result, op = .br depth result
        · obtain ⟨depth, result, rfl⟩ := isBranch
          exact branch_step_iff checked root.found codeTyped
        have notBranch depth result (eq : op = .br depth result) : False := isBranch ⟨_, _, eq⟩
        by_cases isReturn : op = .return_
        case pos =>
          subst op
          constructor
          · intro move
            rcases Computed.lime_body_step_cases move with ⟨_, inside, _⟩ | ⟨_, pop, eq⟩
            · exact (CallFrame.lime_return_stuck (stack := stack) (tail := rest.map limeAdmin.emit) inside).elim
            · exact ⟨_, rule.mpr (.returnLabel locals stack rest),
                eq.trans (by rw [CallFrame.lime_return_label_result pop]; rfl)⟩
          · rintro ⟨out, move, rfl⟩
            cases rule.mp move with
            | returnLabel =>
              simpa only [limeAt, Phase.renderAt, Body.render, limeAdmin, List.map_cons,
                limeEmit, Op.emit, limeCodeSyntax, List.append_assoc, List.singleton_append, n] using
                Step.frame (Step.pure (host := CallFrame.limeNoHost) s (currentFrame target.declaration locals)
                  (.labelReturn n [] stack (rest.map limeAdmin.emit)))
                  n caller
        have stays {out : List Admin} := running_stays (types := (currentFrame target.declaration locals).module.types)
          (n := n) (v := stack) (op := op) (rest := rest) notBranch isReturn (out := out)
        constructor
        · intro move
          obtain ⟨mid, inner, eq⟩ := (under_label_iff stays).mp move
          cases op with
          | br depth result => exact (notBranch depth result rfl).elim
          | return_ => exact (isReturn rfl).elim
          | numeric op =>
            have reduction := (Prefix.lime_step_iff (op := op) (tail := rest.map limeAdmin.emit)).mp inner
            obtain ⟨answer, reduce, rfl⟩ := reduction
            exact ⟨_, rule.mpr (.numeric reduce), eq.trans (by cases answer <;> rfl)⟩
          | set idx =>
            obtain ⟨saved, value, next, rfl, write, rfl⟩ := Computed.lime_set_read (f := currentFrame target.declaration locals) inner
            exact ⟨_, rule.mpr (.localSet write), eq⟩
          | tee idx =>
            obtain ⟨saved, value, rfl, write, rfl⟩ := Computed.lime_tee_read (f := currentFrame target.declaration locals) inner
            exact ⟨_, rule.mpr (.localTee write), eq⟩
          | call child =>
            obtain ⟨saved, operands, rfl, used, count⟩ := split_call codeTyped
            obtain ⟨_, _, _, resolves⟩ := program.linked_target checked root.found used
            have h : (currentFrame target.declaration locals).module.funcs[child.index.toNat]? = some child.address := by
              simpa only [currentFrame, ← root.declared] using resolves
            obtain rfl := (Computed.lime_direct_call_iff (stack := saved ++ operands)
              (tail := rest.map limeAdmin.emit) h).mp inner
            exact ⟨_, rule.mpr (.dispatch locals saved operands child rest used count), eq.trans (by
              simp only [limeAt, Phase.renderAt, Body.render, limeAdmin, values_append, n,
                List.append_assoc, List.singleton_append])⟩
          | if_ result thenBody elseBody =>
            obtain ⟨saved, condition, rfl⟩ := Function.split_if codeTyped
            have select := (Computed.lime_if_iff (s := s) (f := currentFrame target.declaration locals)
              (bt := Blocks.limeType result) (saved := saved) (condition := condition)
              (thenBody := Op.emitList limeCodeSyntax thenBody)
              (elseBody := Op.emitList limeCodeSyntax elseBody) (rest := rest.map limeAdmin.emit)).mp inner
            subst mid
            refine ⟨_, rule.mpr (.ifSelect locals saved condition result thenBody elseBody rest), ?_⟩
            exact eq.trans (by
              simp only [limeAt, Phase.renderAt, Body.render, limeAdmin, limeEmit, Op.emit,
                limeCodeSyntax, Function.comp_def, Op.emitList_selected, List.map_cons, n])
          | block result body =>
            have enter := (Computed.lime_block_iff (result := result)
              (body := Op.emitList limeCodeSyntax body) (stack := stack) (rest := rest.map limeAdmin.emit)).mp inner
            exact ⟨_, rule.mpr (.blockEnter locals stack result body rest), eq.trans (by
              simpa only [limeAt, Phase.renderAt, Body.render, limeAdmin, values, List.map_nil, List.nil_append,
                code_expression, n] using congrArg (fun x : Config H =>
                  (⟨x.store, caller, [.frame n x.frame [.label n [] x.code]]⟩ : Config H)) enter)⟩
          | unreachable =>
            obtain rfl := Computed.lime_unreachable_iff.mp inner
            exact ⟨_, rule.mpr (.unreachable locals stack rest), eq⟩
        · rintro ⟨out, move, rfl⟩
          cases rule.mp move with
          | branchHere | branchOuter => exact (isBranch ⟨_, _, rfl⟩).elim
          | returnLabel => exact (isReturn rfl).elim
          | @numeric locals stack op rest answer reduce =>
            apply lift_label
            exact (Prefix.lime_step_iff (s := s) (f := currentFrame target.declaration locals) (stack := stack)
              (op := op) (tail := rest.map limeAdmin.emit)).mpr ⟨answer, reduce, by cases answer <;> rfl⟩
          | @localSet locals next saved i value rest write =>
            exact lift_label (set_sound write)
          | @localTee locals saved i value rest write =>
            exact lift_label (tee_sound write)
          | dispatch _ saved operands child rest used count =>
            obtain ⟨_, _, _, resolves⟩ := program.linked_target checked root.found used
            have h : (currentFrame target.declaration locals).module.funcs[child.index.toNat]? = some child.address := by
              simpa only [currentFrame, ← root.declared] using resolves
            apply lift_label
            simpa only [Body.render, Phase.render, Phase.renderAt, limeAdmin, limeEmit, Op.emit, limeCodeSyntax, Sequence.limeSource, Function.comp_def, values_append, List.map_cons, List.append_assoc, List.singleton_append] using
              (Computed.lime_direct_call_iff (stack := saved ++ operands) (tail := rest.map limeAdmin.emit) h).mpr rfl
          | @ifSelect locals saved condition result thenBody elseBody rest =>
            apply lift_label
            have select := (Computed.lime_if_iff (s := s) (f := currentFrame target.declaration locals)
              (bt := Blocks.limeType result) (saved := saved)
              (condition := condition)
              (thenBody := Op.emitList limeCodeSyntax thenBody)
              (elseBody := Op.emitList limeCodeSyntax elseBody) (rest := rest.map limeAdmin.emit)).mpr rfl
            simpa only [Body.render, limeAdmin, limeEmit, Op.emit, limeCodeSyntax, Function.comp_def,
              Op.emitList_selected, List.map_cons, List.map_append, List.map_nil] using select
          | blockEnter =>
            rename_i result body
            apply lift_label
            exact (Computed.lime_block_iff (result := result) (body := Op.emitList limeCodeSyntax body)
              (stack := stack) (rest := rest.map limeAdmin.emit)).mpr (by rw [code_expression]; rfl)
          | unreachable =>
            exact lift_label (Computed.lime_unreachable_iff.mpr rfl)
    | @active _ _ _ locals saved child q rest callee typed used childFound declared live childReady resume =>
      obtain ⟨_, _, _, resolves⟩ := program.linked_target checked root.found used
      have childResolves : child.Resolves (currentFrame target.declaration locals) := by
        simpa only [CallTarget.Resolves, currentFrame, ← root.declared] using resolves
      have childStep {next : Config H} := descend child used
        (dst := next) ⟨childFound, declared, childResolves⟩ childReady
      cases q with
      | call | branching | done => cases live
      | invoke operands =>
        cases childReady with
        | invoke localsTyped => exact pending_child_iff checked n allocated root.found used childFound declared localsTyped
      | label | returning | exit => exact active_entered_iff checked n root.found used live rfl childStep
    | @trapped _ _ _ locals saved rest typed =>
      constructor
      · intro move
        rcases Computed.lime_body_step_cases move with ⟨mid, inside, eq⟩ | ⟨_, pop, eq⟩
        · obtain ⟨kept, remaining, cut, rfl⟩ := (Prefix.lime_discard_iff limeAdmin.emit).mp inside
          exact ⟨_, rule.mpr (.discard cut), eq⟩
        · obtain ⟨rfl, rfl⟩ := trapped_not_final pop
          exact ⟨_, rule.mpr (.leaveTrap locals), eq.trans (by rw [Nested.lime_label_result (r := .trap) pop]; rfl)⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | discard cut => exact lift_label ((Prefix.lime_discard_iff limeAdmin.emit).mpr ⟨_, _, cut, rfl⟩)
        | leaveTrap => exact .frame (.pure s _ (.labelTrap _ [])) _ caller
    | @block _ _ _ locals saved result inside rest innerTyped resume =>
      have smaller : sizeOf inside < size := by rw [← sizeEq]; simp [Body.block.sizeOf_spec]; omega
      exact block_step_iff checked root.found (n := n) (fun {dst} =>
        ih (sizeOf inside) smaller (dst := dst) rfl innerTyped)

theorem step_iff {H : Type} {s : Store H} {program : Program} (checked : program.check = true)
    (allocated : program.LimeAllocated s) (address : FuncAddr) :
    ∀ {caller target fn a dst}, (addr : target.address = address) →
      Root program caller target fn → Admitted program fn a →
      (Step CallFrame.limeNoHost (limeConfig s caller target a) dst ↔
        ∃ out, program.Edge checked target.address a out ∧ dst = limeConfig s caller target out) := by
  induction address using (program.table.wellFounded (Program.rankCheck checked)).induction with
  | h address ih =>
    intro caller target fn a dst addr root ready
    subst address
    have rule {a b : Phase} := program.edge_iff checked (a := a) (b := b) root.found
    have callLookup : caller.module.funcs[target.index.toNat]? = some target.address := root.resolves
    have descend child (used : child ∈ fn.targets) {parent callee q dst} (childRoot : Root program parent child callee)
        (childReady : Admitted program callee q) :=
      ih child.address (program.target_resolved checked root.found used) (dst := dst) rfl childRoot childReady
    have region {locals body} (ok : Admitted program fn (.label locals body)) :
        native (limeConfig s caller target (.label locals body)) dst ↔
          ∃ out, program.Edge checked target.address (.label locals body) out ∧ dst = limeConfig s caller target out := by
      simpa only [limeConfig, limeAt, Phase.render, root.declared] using
        region_step_iff checked allocated root descend (sizeOf body) (dst := dst) rfl ok
    cases ready with
    | @call _ args typed =>
      have move := Computed.lime_direct_call_iff (s := s) (stack := args) (tail := []) (dst := dst) callLookup
      constructor
      · intro h
        exact ⟨_, rule.mpr (.resolve args), move.mp h⟩
      · rintro ⟨out, h, rfl⟩
        cases rule.mp h with
        | resolve => exact (Computed.lime_direct_call_iff callLookup).mpr rfl
    | @invoke _ args typed =>
      have move := entry_iff (caller := caller) (saved := []) (rest := []) (dst := dst) root.declared
        (allocated _ _ root.found) typed
      constructor
      · intro step
        refine ⟨_, rule.mpr (.enter args typed), ?_⟩
        exact (move.mp step).trans (by simp [limeConfig, values])
      · rintro ⟨out, step, rfl⟩
        cases rule.mp step with
        | enter =>
          change native ⟨s, caller, values args ++ [.invoke target.address]⟩
            ⟨s, caller, (Phase.label (fn.declaration.frame args).locals (.running fn.initial fn.code)).render limeAdmin target⟩
          simpa only [values, List.map_nil, List.nil_append, List.append_nil] using
            (entry_iff (caller := caller) (saved := []) (rest := []) root.declared (allocated _ _ root.found) typed).mpr rfl
    | running typed code => exact region (.running typed code)
    | active typed used found declared live ready resume => exact region (.active typed used found declared live ready resume)
    | block inside resume => exact region (.block inside resume)
    | trapped typed => exact region (.trapped typed)
    | @returning _ _ _ locals stack typed returnTyped =>
      constructor
      · intro move
        obtain ⟨extra, results, rfl, arity⟩ := split_return returnTyped
        have count := arity.trans (congrArg (fun d => d.results.length) root.declared)
        exact ⟨_, rule.mpr (.returnFrame locals extra results arity),
          (CallFrame.lime_return_frame_iff count).mp move⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | returnFrame locals dropped returned arity =>
          exact (CallFrame.lime_return_frame_iff
            (arity.trans (congrArg (fun d => d.results.length) root.declared))).mpr rfl
    | @exit _ _ _ locals result typed outTyped =>
      constructor
      · intro move
        exact ⟨_, rule.mpr (.leaveFrame locals result outTyped), Nested.lime_frame_result move⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | leaveFrame =>
          cases result with
          | trap => exact .pure s caller (.frameTrap _ _)
          | values xs =>
            exact .pure s caller (.frameDone _ _ xs ((result_length outTyped).trans
              (congrArg (fun d => d.results.length) root.declared)))
    | branching _ target _ => simp at target
    | @done _ _ _ result typed =>
      constructor
      · intro step
        exact (Nested.lime_result_stuck step).elim
      · rintro ⟨_, step, _⟩
        cases rule.mp step

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.Lime1
