module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source

open Silmaril.Semantics.SOS

theorem fact {call : Invocation} {a b : State call} (rule : Ground call a b) : Edge call a b :=
  Derives.apply (R := (presentation call).rules) (r := ⟨[], .step a b⟩) (.ground rule) (by simp)

theorem framed {call : Invocation} {a b : Framed.State call.context call.body.invocation.site}
    (edge : Framed.Edge call.context call.body.invocation a b) : Edge call (.framed a) (.framed b) :=
  Proofs.framed edge

theorem framed_run {call : Invocation} {a b : Framed.State call.context call.body.invocation.site}
    (run : Framed.Runs call.context call.body.invocation a b) : Runs call (.framed a) (.framed b) :=
  Proofs.framed_run run

theorem enter_run {call : Invocation} {b : Framed.State call.context call.body.invocation.site}
    (run : Framed.Runs call.context call.body.invocation call.start b) : Runs call .call (.framed b) :=
  ((Relation.ReflTransGen.single (fact .resolve)).tail (fact .enter)).trans (framed_run run)

theorem closed {call : Invocation} (typed : Typed call) (program : DirectSequence.Typed call.body.invocation)
    (targets : call.body.invocation.site.body.TypedTargets) (suffix : call.context.sequence.TypedTargets)
    {a b : State call} (ready : Admitted a) (edge : Edge call a b) : Admitted b :=
  Proofs.closed typed program targets suffix ready edge

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source
