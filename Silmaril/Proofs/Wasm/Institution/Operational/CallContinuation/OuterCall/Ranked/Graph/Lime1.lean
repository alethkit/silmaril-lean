module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Context
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.NativeCommon
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution
open Execution.Runtime (Frame FuncAddr Value)
open Computed

private abbrev native {H : Type} := Step (H := H) CallFrame.limeNoHost

private theorem expression_code (fn : Function) :
    expression fn.limeFunc.body = (Body.running fn.initial fn.code).render limeAdmin := by
  change expression (fn.instructions Sequence.limeSource (Locals.limeInstr ∘ .set) (Locals.limeInstr ∘ .tee) .unreachable) = _
  rw [Function.instructions, expression_append]
  change (fn.initial.map Sequence.limeSource.value).map Runtime.AdminInstr.source ++
      (fn.code.map (Op.emit Sequence.limeSource (Locals.limeInstr ∘ .set) (Locals.limeInstr ∘ .tee) .unreachable)).map Runtime.AdminInstr.source =
    values fn.initial ++ fn.code.map limeAdmin.emit
  rw [List.map_map, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro v _
    rcases v with ⟨t, bits⟩
    cases t <;> rfl
  · apply List.map_congr_left
    intro op _
    cases op with
    | numeric op => cases op <;> rfl
    | set | tee | call | unreachable => rfl

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
    Locals.limeInstr, currentFrame, Body.render, limeAdmin, Syntax.emit, Op.emit,
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
    Locals.limeInstr, currentFrame, Body.render, limeAdmin, Syntax.emit, Op.emit,
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
    rw [expression_code, Phase.render, ← declared]
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
    (pop : PureStep types [.label n [] ((Body.running v (op :: rest)).render limeAdmin)] out) : False := by
  change PureStep types [.label n [] (values v ++ limeAdmin.emit op :: rest.map limeAdmin.emit)] out at pop
  cases op with
  | numeric p =>
    cases p <;> exact Computed.lime_label_stays (head := limeAdmin.emit (.numeric _)) (by rfl)
      (by simp [Syntax.emit, Op.emit, limeAdmin, Prefix.emit, limeSyntax])
      (by simp [Syntax.emit, Op.emit, limeAdmin, Prefix.emit, limeSyntax])
      (by simp [Syntax.emit, Op.emit, limeAdmin, Prefix.emit, limeSyntax]) pop
  | set idx =>
    exact Computed.lime_label_stays (head := .source (.localSet idx)) rfl (by simp) (by simp) (by simp) pop
  | tee idx =>
    exact Computed.lime_label_stays (head := .source (.localTee idx)) rfl (by simp) (by simp) (by simp) pop
  | call t => exact Computed.lime_label_stays (head := .source (.call t.index)) rfl (by simp) (by simp) (by simp) pop
  | unreachable => exact Computed.lime_label_stays (head := .source .unreachable) rfl (by simp) (by simp) (by simp) pop

private theorem active_entered_iff {H : Type} {s : Store H} {program : Program} (checked : program.check = true)
    {caller : Frame} {root target : CallTarget} {fn : Function}
    (found : program.lookup root.address = some fn) (used : target ∈ fn.targets)
    {locals saved : List Value} {rest : List Op} {child : Phase} (live : child.Active)
    {k : Nat} {f : Frame} {code : List Admin} (rendered : child.render limeAdmin target = [.frame k f code])
    (childStep : ∀ {dst}, native (limeConfig s (currentFrame root.declaration locals) target child) dst ↔
      ∃ out, program.Edge checked target.address child out ∧ dst = limeConfig s (currentFrame root.declaration locals) target out)
    {dst : Config H} :
    native (limeConfig s caller root (.label locals (.active saved target child rest))) dst ↔
      ∃ out, program.Edge checked root.address (.label locals (.active saved target child rest)) out ∧
        dst = limeConfig s caller root out := by
  have ctx : native (limeConfig s caller root (.label locals (.active saved target child rest))) dst ↔
      ∃ mid, native (limeConfig s (currentFrame root.declaration locals) target child) mid ∧
        dst = ⟨mid.store, caller, [.frame root.declaration.results.length mid.frame
          [.label root.declaration.results.length [] (values saved ++ mid.code ++ rest.map limeAdmin.emit)]]⟩ := by
    change native ⟨s, caller, [.frame root.declaration.results.length (currentFrame root.declaration locals)
        [.label root.declaration.results.length [] (values saved ++ child.render limeAdmin target ++ rest.map limeAdmin.emit)]]⟩ dst ↔
      ∃ mid, native ⟨s, currentFrame root.declaration locals, child.render limeAdmin target⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame root.declaration.results.length mid.frame
          [.label root.declaration.results.length [] (values saved ++ mid.code ++ rest.map limeAdmin.emit)]]⟩
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

private theorem pending_child_iff {H : Type} {s : Store H} {program : Program} (checked : program.check = true)
    (allocated : program.LimeAllocated s) {caller : Frame} {root target : CallTarget} {fn callee : Function}
    (found : program.lookup root.address = some fn) (used : target ∈ fn.targets)
    (childFound : program.lookup target.address = some callee) (declared : callee.declaration = target.declaration)
    {locals saved operands : List Value} {rest : List Op} (typed : operands.map Value.type = callee.declaration.params)
    {dst : Config H} :
    native (limeConfig s caller root (.label locals (.active saved target (.invoke operands) rest))) dst ↔
      ∃ out, program.Edge checked root.address (.label locals (.active saved target (.invoke operands) rest)) out ∧
        dst = limeConfig s caller root out := by
  have stays {out : List Admin} (pop : PureStep (currentFrame root.declaration locals).module.types
      [.label root.declaration.results.length []
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
    | @running _ locals stack rest typed codeTyped =>
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
            simpa only [limeConfig, Phase.render, Body.render, limeAdmin, List.map_nil, List.append_nil, Nested.resultCode] using
              Step.frame (Step.pure (host := CallFrame.limeNoHost) s (currentFrame target.declaration locals)
                (.labelDone target.declaration.results.length [] stack)) target.declaration.results.length caller
      | cons op rest =>
        have stays {out : List Admin} := running_stays (types := (currentFrame target.declaration locals).module.types)
          (n := target.declaration.results.length) (v := stack) (op := op) (rest := rest) (out := out)
        constructor
        · intro move
          obtain ⟨mid, inner, eq⟩ := (under_label_iff stays).mp move
          cases op with
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
              simp only [limeConfig, Phase.render, Body.render, limeAdmin, values_append,
                List.append_assoc, List.singleton_append])⟩
          | unreachable =>
            obtain rfl := Computed.lime_unreachable_iff.mp inner
            exact ⟨_, rule.mpr (.unreachable locals stack rest), eq⟩
        · rintro ⟨out, move, rfl⟩
          cases rule.mp move with
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
            simpa only [Body.render, Phase.render, limeAdmin, Syntax.emit, Op.emit, limeSyntax, Function.comp_def, values_append, List.map_cons, List.append_assoc, List.singleton_append] using
              (Computed.lime_direct_call_iff (stack := saved ++ operands) (tail := rest.map limeAdmin.emit) h).mpr rfl
          | unreachable =>
            exact lift_label (Computed.lime_unreachable_iff.mpr rfl)
    | @active _ locals saved child q rest callee typed used childFound declared live childReady resume =>
      obtain ⟨_, _, _, resolves⟩ := program.linked_target checked root.found used
      have childResolves : child.Resolves (currentFrame target.declaration locals) := by
        simpa only [CallTarget.Resolves, currentFrame, ← root.declared] using resolves
      have childStep {next : Config H} := ih child.address (program.target_resolved checked root.found used)
        (dst := next) rfl ⟨childFound, declared, childResolves⟩ childReady
      cases q with
      | call | done => cases live
      | invoke operands =>
        cases childReady with
        | invoke localsTyped => exact pending_child_iff checked allocated root.found used childFound declared localsTyped
      | label | exit => exact active_entered_iff checked root.found used live rfl childStep
    | @trapped _ locals saved rest typed =>
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
    | @exit _ locals result typed outTyped =>
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
    | @done _ result typed =>
      constructor
      · intro step
        exact (Nested.lime_result_stuck step).elim
      · rintro ⟨_, step, _⟩
        cases rule.mp step

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.Lime1
