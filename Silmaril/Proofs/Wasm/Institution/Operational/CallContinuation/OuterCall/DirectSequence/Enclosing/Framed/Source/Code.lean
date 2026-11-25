module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs

open Execution
open Execution.Runtime (Value)
open StraightLine
open Computed (ArgumentSyntax v1Syntax limeSyntax coreSyntax)
open Computed.Sequence (v1Source limeSource coreSource)

theorem map_code {A B : Type} {decl : Declaration} (body : Body decl) (sourceOps : ArgumentSyntax A)
    (targetOps : ArgumentSyntax B) (translate : A → B)
    (value : ∀ v, translate (sourceOps.value v) = targetOps.value v)
    (get : ∀ i, translate (sourceOps.get i) = targetOps.get i)
    (binary : ∀ t op, translate (sourceOps.binary t op) = targetOps.binary t op)
    (call : ∀ i, translate (sourceOps.call i) = targetOps.call i) :
    (body.code sourceOps).map translate = body.code targetOps := by
  have front (stack : List Value) :
      stack.map (translate ∘ sourceOps.value) = stack.map targetOps.value :=
    List.map_congr_left fun v _ => value v
  have suffix : body.continuation.map (translate ∘ Sequence.emit sourceOps) =
      body.continuation.map (Sequence.emit targetOps) := by
    apply List.map_congr_left
    intro op _
    cases op with
    | call i => exact call _
    | numeric op =>
      cases op with
      | get i => exact get i
      | bin t op => exact binary t op
  simp only [Body.code, List.map_append, List.map_cons, List.map_map, call, front, suffix]

private theorem continuation_code {A : Type} {decl : Declaration} (body : Body decl)
    (args : List Value) (ops : ArgumentSyntax A) :
    (body.context args).continuation.map (Sequence.emit ops) = body.continuation.map (Sequence.emit ops) := by
  simp only [Body.context, List.map_map]
  apply List.map_congr_left
  intro op _
  cases op <;> rfl

theorem v1_expression (call : Invocation) :
    Wasm.V1.Execution.expression call.body.v1Func.body =
      Enclosing.v1Code call.context call.body.invocation.site (.active .call) := by
  change (call.body.code v1Source).map Execution.Runtime.AdminInstr.source = _
  rw [map_code call.body v1Source v1Syntax Execution.Runtime.AdminInstr.source
    (fun ⟨t, bits⟩ => by cases t <;> rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
  have tail := continuation_code call.body call.args v1Syntax
  change call.body.code v1Syntax = Wasm.V1.Execution.values call.body.saved ++ DirectSequence.v1Code call.body.invocation.site .call ++
    call.context.continuation.map (Sequence.emit v1Syntax)
  rw [show call.context.continuation.map (Sequence.emit v1Syntax) =
    call.body.continuation.map (Sequence.emit v1Syntax) from tail]
  change Wasm.V1.Execution.values (call.body.saved ++ call.body.invocation.site.args) ++ _ = _
  simp only [DirectSequence.v1Code, DirectSequence.render, Wasm.V1.Execution.values_append, List.append_assoc, List.singleton_append]
  rfl

theorem lime_expression (call : Invocation) :
    Wasm.Lime1.Execution.expression call.body.limeFunc.body =
      Enclosing.limeCode call.context call.body.invocation.site (.active .call) := by
  change (call.body.code limeSource).map Execution.Runtime.AdminInstr.source = _
  rw [map_code call.body limeSource limeSyntax Execution.Runtime.AdminInstr.source
    (fun ⟨t, bits⟩ => by cases t <;> rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
  have tail := continuation_code call.body call.args limeSyntax
  change call.body.code limeSyntax = Wasm.Lime1.Execution.values call.body.saved ++ DirectSequence.limeCode call.body.invocation.site .call ++
    call.context.continuation.map (Sequence.emit limeSyntax)
  rw [show call.context.continuation.map (Sequence.emit limeSyntax) =
    call.body.continuation.map (Sequence.emit limeSyntax) from tail]
  change Wasm.Lime1.Execution.values (call.body.saved ++ call.body.invocation.site.args) ++ _ = _
  simp only [DirectSequence.limeCode, DirectSequence.render, Wasm.Lime1.Execution.values_append, List.append_assoc, List.singleton_append]
  rfl

theorem core_expression (call : Invocation) :
    Core.expression call.body.coreFunc.body =
      Enclosing.coreCode call.context call.body.invocation.site (.active .call) := by
  change (call.body.code coreSource).map Core.Admin.plain = _
  rw [map_code call.body coreSource coreSyntax Core.Admin.plain
    (fun ⟨t, bits⟩ => by cases t <;> rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
  have tail := continuation_code call.body call.args coreSyntax
  change call.body.code coreSyntax = coreValues call.body.saved ++ DirectSequence.coreCode call.body.invocation.site .call ++
    call.context.continuation.map (Sequence.emit coreSyntax)
  rw [show call.context.continuation.map (Sequence.emit coreSyntax) =
    call.body.continuation.map (Sequence.emit coreSyntax) from tail]
  have emitted (stack : List Value) : stack.map coreSyntax.value = coreValues stack := by
    simp only [coreValues, Core.vals, List.map_map]
    rfl
  rw [Body.code, emitted]
  simp only [DirectSequence.coreCode, DirectSequence.render, coreValues, List.map_append, Core.vals_append, List.append_assoc, List.singleton_append]
  rfl

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs
