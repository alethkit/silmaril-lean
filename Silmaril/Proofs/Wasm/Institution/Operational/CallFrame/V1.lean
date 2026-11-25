module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallFrame.Thms
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Rules
public import Silmaril.Wasm.Versions.Lime1.Execution.Thms
public import Silmaril.Wasm.RuntimeMap.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame.Proofs.V1

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution.Runtime

private abbrev bodyCode : Body → List Admin :=
  legacyBody Locals.v1Instr .return_ .unreachable

private abbrev exitCode : Exit → List Admin := legacyExit value .return_

private theorem encode_values (vs : List Value) :
    Locals.v1Codec.encode (Locals.values vs) = values vs := by
  have emit (v : Value) : Locals.v1Codec.emit (.value v) = value v := by
    rcases v with ⟨t, bits⟩
    cases t <;> rfl
  simp [Locals.Codec.encode, Locals.values, values, List.map_map, emit]

@[local simp] private theorem body_locals (code : List Locals.Op) :
    bodyCode (.code (.locals code)) = Locals.v1Codec.encode code := List.map_map

@[local simp] private theorem body_return (stack : List Value) :
    bodyCode (.code (.ret stack)) = values stack ++ [.source .return_] := by
  simp only [legacyBody, Program.instructions, List.map_append, List.map_cons, List.map_nil]
  rw [List.map_map, ← encode_values]
  rfl

private theorem context_step {H : Type} (saved : List Value) {a b : Config H}
    (h : Step v1NoHost a b) :
    Step v1NoHost ⟨a.store, a.frame, values saved ++ a.code⟩ ⟨b.store, b.frame, values saved ++ b.code⟩ := by
  cases a
  cases b
  simpa only [List.append_nil] using Step.context h saved []

theorem sound {H : Type} {s : Store H} {caller : Frame} {address : FuncAddr} {fn : Callee}
    (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a b : State} (step : Edge fn a b) :
    Step v1NoHost (v1Config s caller address fn a) (v1Config s caller address fn b) := by
  cases invert step with
  | @reduce saved before after h =>
    have inner := Locals.v1_sound (s := s) (m := fn.module) (host := v1NoHost) h
    simpa [v1Config, v1Code, legacyCode, values, Callee.frame] using
      context_step saved (.frame (.label inner fn.arity []) fn.arity caller)
  | fact h =>
    cases h with
    | enter saved args arity =>
      have h := Step.invokeWasm (host := v1NoHost) s caller address fn.type fn.module fn.v1Func
        args allocated arity (by change fn.result.toList.length ≤ 1; cases fn.result <;> simp)
      simpa [v1Config, v1Code, legacyCode, Callee.v1Func, Callee.init, Callee.frame, Callee.type,
        Callee.arity, expression, values, List.map_append, List.append_assoc, legacyBody] using context_step saved h
    | unreachable saved ls =>
      have h := Step.pure (host := v1NoHost) s (fn.frame ls) PureStep.unreachable
      simpa [v1Config, v1Code, legacyCode, legacyBody, Program.instructions, values] using
        context_step saved (.frame (.label h fn.arity []) fn.arity caller)
    | labelValues saved ls stack =>
      have h := Step.pure (host := v1NoHost) s (fn.frame ls) (PureStep.labelDone fn.arity [] stack)
      simpa [v1Config, v1Code, legacyCode, legacyExit, encode_values, values] using
        context_step saved (.frame h fn.arity caller)
    | labelReturn saved ls stack =>
      have h := Step.pure (host := v1NoHost) s (fn.frame ls) (PureStep.labelReturn fn.arity [] stack [])
      simpa [v1Config, v1Code, legacyCode, legacyExit, values] using
        context_step saved (.frame h fn.arity caller)
    | labelTrap saved ls =>
      have h := Step.pure (host := v1NoHost) s (fn.frame ls) (PureStep.labelTrap fn.arity [])
      simpa [v1Config, v1Code, legacyCode, legacyBody, legacyExit, values] using
        context_step saved (.frame h fn.arity caller)
    | frameValues saved ls stack arity =>
      have h := Step.pure (host := v1NoHost) s caller (PureStep.frameDone fn.arity (fn.frame ls) stack arity)
      simpa [v1Config, v1Code, legacyCode, legacyExit, values, List.map_append] using context_step saved h
    | frameReturn saved ls extra results arity =>
      have h := Step.pure (host := v1NoHost) s caller
        (PureStep.frameReturn fn.arity (fn.frame ls) extra results [] arity)
      simpa [v1Config, v1Code, legacyCode, legacyExit, values, List.map_append, List.append_assoc] using
        context_step saved h
    | frameTrap saved ls =>
      have h := Step.pure (host := v1NoHost) s caller (PureStep.frameTrap fn.arity (fn.frame ls))
      simpa [v1Config, v1Code, legacyCode, legacyExit, values] using context_step saved h
    | bubble saved discarded ne =>
      cases discarded with
      | nil => exact (ne rfl).elim
      | cons v vs =>
        have h := Step.pure (host := v1NoHost) s caller (PureStep.trapValues v vs [])
        simpa [v1Config, v1Code, legacyCode, values, List.map_append, List.append_assoc] using context_step saved h

private theorem config_toLime_injective (H : Type) :
    Function.Injective (Config.toLime (H := H)) := by
  rintro ⟨s, f, xs⟩ ⟨t, g, ys⟩ eq
  have stores := RuntimeMap.store_mapCode_injective Wasm.V1.Func.toLime_injective
    (congrArg (fun c : Wasm.Lime1.Execution.Config H => c.store) eq)
  have frames : f = g := congrArg (fun c : Wasm.Lime1.Execution.Config H => c.frame) eq
  have codes := RuntimeMap.adminInstr_mapList_injective Wasm.V1.Instr.toLime_injective xs ys
    (congrArg (fun c : Wasm.Lime1.Execution.Config H => c.code) eq)
  cases stores
  cases frames
  cases codes
  rfl

theorem readback {H : Type} {s : Store H} {caller : Frame} {address : FuncAddr} {fn : Callee}
    (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {dst : Config H} (ready : Admitted fn a)
    (step : Step v1NoHost (v1Config s caller address fn a) dst) :
    ∃ out, Edge fn a out ∧ dst = v1Config s caller address fn out := by
  have translated := step.toLime (target := limeNoHost) (fun _ _ _ _ impossible => impossible)
  rw [Proofs.v1_to_lime] at translated
  obtain ⟨out, rule, eq⟩ := Proofs.Lime1.readback (Proofs.allocated_toLime allocated) ready translated
  refine ⟨out, rule, config_toLime_injective H ?_⟩
  rw [Proofs.v1_to_lime]
  exact eq

end Silmaril.Wasm.Institution.Operational.CallFrame.Proofs.V1
