module

public import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Value)

private theorem encode_values (xs : List Value) :
    Locals.limeCodec.encode (Locals.values xs) = values xs := by
  unfold Locals.Codec.encode Locals.values
  rw [List.map_map]
  simp only [Locals.limeCodec, Locals.legacyCodec, Locals.limeInstr, values]
  apply List.map_congr_left
  intro v _
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

private theorem source_iff {H : Type} {s : Store H} {site : Site}
    {locals args : List Value} {body : Body} {dst : Config H} (resolved : site.Resolved)
    (arity : args.length = site.signature.params.length) :
    Step CallFrame.limeNoHost (limeConfig s site (.source locals args body)) dst ↔
      dst = limeConfig s site (body.entered locals args) := by
  have lookup : blockType? site.declaration.module.types (.typeIdx site.index) = some site.signature := resolved
  let code := body.instructions Locals.limeInstr (.br ⟨0⟩) .return_
  have before : limeConfig s site (.source locals args body) =
      ⟨s, ⟨locals, site.declaration.module⟩, values (site.saved ++ args) ++ [.source (.block (.typeIdx site.index) code)]⟩ := by
    simp [limeConfig, State.frame, State.code, limeSyntax, code, values_append, List.append_assoc]
  have after : limeConfig s site (body.entered locals args) =
      ⟨s, ⟨locals, site.declaration.module⟩, values site.saved ++
        [.label site.signature.results.length [] (values args ++ expression code)]⟩ := by
    cases body with
    | locals bodyCode =>
      have encoded : Locals.limeCodec.encode bodyCode = expression code := by
        change bodyCode.map (Execution.Runtime.AdminInstr.source ∘ Locals.limeInstr) =
          (bodyCode.map Locals.limeInstr).map Execution.Runtime.AdminInstr.source
        exact (List.map_map ..).symm
      simp only [limeConfig, State.frame, State.code, limeSyntax, Body.entered,
        Locals.Codec.encode_append, encode_values, encoded]
    | branch | return_ => rfl
  rw [before, after, CallContinuation.OuterCall.Computed.lime_block_step_iff]
  constructor
  · rintro ⟨saved, used, ft, split, found, size, rfl⟩
    rw [lookup] at found
    cases found
    obtain ⟨rfl, rfl⟩ := List.append_inj' split (arity.trans size.symm)
    simp
  · intro eq
    exact ⟨site.saved, args, site.signature, rfl, lookup, arity,
      by simpa using eq⟩

theorem step_iff {H : Type} {s : Store H} {site : Site} {a : State}
    {dst : Config H} (ready : Admitted site a) :
    Step CallFrame.limeNoHost (limeConfig s site a) dst ↔
      ∃ out, Edge site a out ∧ dst = limeConfig s site out := by
  cases a with
  | source locals args body =>
    have arity : args.length = site.signature.params.length := by
      simpa using congrArg List.length ready.2.2.1
    rw [source_iff ready.1 arity]
    constructor
    · intro eq
      exact ⟨_, .enter locals args body, eq⟩
    · rintro ⟨_, edge, eq⟩
      cases edge
      exact eq
  | label a =>
    change Step CallFrame.limeNoHost
      ⟨s, ⟨a.locals, site.declaration.module⟩, values site.saved ++
        .label site.signature.results.length [] (Locals.limeCodec.encode a.code) :: []⟩ dst ↔ _
    rw [Blocks.Context.lime_label_iff]
    simp only [List.append_nil]
    constructor
    · rintro (⟨mid, inside, rfl⟩ | ⟨code, pop, rfl⟩)
      · obtain ⟨next, edge, rfl⟩ := Locals.lime_step_iff.mp inside
        exact ⟨.label next, .reduce edge, rfl⟩
      · obtain ⟨results, code, rfl⟩ := Blocks.lime_locals_label_exit pop
        have same : a = ⟨a.locals, Locals.values results⟩ := by cases a; simp_all
        exact ⟨.done a.locals results, same.symm ▸ .fallthrough _ _, rfl⟩
    · rintro ⟨out, edge, rfl⟩
      cases edge with
      | reduce move => exact .inl ⟨_, Locals.lime_sound move, rfl⟩
      | fallthrough locals results =>
        refine .inr ⟨_, ?_, rfl⟩
        rw [encode_values]
        exact PureStep.labelDone (types := site.declaration.module.types) site.signature.results.length [] results
  | branch locals stack =>
    change Step CallFrame.limeNoHost ⟨s, ⟨locals, site.declaration.module⟩, values site.saved ++
      .label site.signature.results.length [] (values stack ++ [.source (.br ⟨0⟩)]) :: []⟩ dst ↔ _
    rw [Blocks.Context.lime_label_iff]
    simp only [List.append_nil]
    constructor
    · rintro (⟨mid, inside, _⟩ | ⟨code, pop, rfl⟩)
      · exact (BranchExit.lime_br_vals_stuck inside).elim
      · obtain ⟨scratch, payload, split, size, rfl⟩ := BranchExit.lime_label_br_zero pop
        refine ⟨.done locals payload, ?_, by simp [limeConfig, State.code, State.frame, limeSyntax]⟩
        rw [split]
        exact .branch locals scratch payload size
    · rintro ⟨out, edge, rfl⟩
      cases edge with
      | branch locals scratch results arity =>
        refine .inr ⟨_, ?_, rfl⟩
        simpa only [limeSyntax, values_append, List.append_assoc,
          List.singleton_append, expression, List.map_nil, List.append_nil] using
          PureStep.labelBranch (types := site.declaration.module.types) _ [] scratch results [] arity
  | return_ locals stack =>
    change Step CallFrame.limeNoHost ⟨s, ⟨locals, site.declaration.module⟩, values site.saved ++
      .label site.signature.results.length [] (values stack ++ [.source .return_]) :: []⟩ dst ↔ _
    rw [Blocks.Context.lime_label_iff]
    simp only [List.append_nil]
    constructor
    · rintro (⟨mid, inside, _⟩ | ⟨code, pop, rfl⟩)
      · exact (CallFrame.lime_return_stuck inside).elim
      · rw [CallFrame.lime_return_label_result (tail := []) pop]
        exact ⟨_, .return_ locals stack, rfl⟩
    · rintro ⟨out, edge, rfl⟩
      cases edge with
      | return_ =>
        refine .inr ⟨_, ?_, rfl⟩
        simpa only [List.append_nil, limeSyntax] using
          (PureStep.labelReturn (types := site.declaration.module.types) site.signature.results.length [] stack [])
  | done locals results =>
    constructor
    · intro move
      have inside : Step CallFrame.limeNoHost ⟨s, ⟨locals, site.declaration.module⟩, values (site.saved ++ results)⟩ dst := by
        simpa [limeConfig, State.code, State.frame, limeSyntax, values_append] using move
      exact (CallContinuation.Nested.lime_result_stuck (r := .values (site.saved ++ results)) inside).elim
    · rintro ⟨_, edge, _⟩
      cases edge
  | pendingReturn locals stack =>
    constructor
    · intro move
      have inside : Step CallFrame.limeNoHost ⟨s, ⟨locals, site.declaration.module⟩,
          values (site.saved ++ stack) ++ [.source .return_]⟩ dst := by
        simpa [limeConfig, State.code, State.frame, limeSyntax, values_append, List.append_assoc] using move
      exact (CallFrame.lime_return_stuck (tail := []) inside).elim
    · rintro ⟨_, edge, _⟩
      cases edge

end Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Proofs.Lime1
