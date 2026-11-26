module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Execution.Defs
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution.Body
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution.Determinism
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution.Fragment
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution.Invoke

public section

namespace Silmaril.MLIR.WasmSSA

open Silmaril.Wasm (TypeIdx)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Context Expand)

/-- Any step of flat integer body code preserves the fragment and the store.
The same transition exists for every numeric profile and host relation. -/
theorem IntBodyCode.step {H : Type} {P Q : Profile} {host host' : HostSemantics H}
    {source target : Config H} (body : IntBodyCode source.code) (step : Step P host source target) :
    target.store = source.store ∧ IntBodyCode target.code ∧ Step Q host' source target :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.intBody_step step body

theorem IntBodyCode.step_unique {H : Type} {P : Profile} {host : HostSemantics H}
    {source left right : Config H} (body : IntBodyCode source.code)
    (h₁ : Step P host source left) (h₂ : Step P host source right) : left = right :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.intBody_step_unique body h₁ h₂

theorem IntBodyCode.steps {H : Type} {P : Profile} {host : HostSemantics H}
    {source target : Config H} (body : IntBodyCode source.code) (run : Steps P host source target) :
    target.store = source.store ∧ IntBodyCode target.code :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.intBody_steps body run

theorem Func.toWasm_intBody {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (type : TypeIdx) (fits : f.Fits) :
    IntBodyCode (expression (f.toWasm C type fits).body) :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.toWasm_intBody f C type fits

/-- Any reachable configuration with no successor is the specified endpoint. -/
theorem CompletesAt.eq_of_stopped {H : Type} {P : Profile} {host : HostSemantics H}
    {start finish c : Config H} (execution : CompletesAt P host start finish)
    (reached : Steps P host start c) (stopped : ∀ next, ¬ Step P host c next) : c = finish := by
  rcases (execution.continues c reached).cases_head with same | ⟨_, step, _⟩
  · exact same
  · exact (stopped _ step).elim

/-- With typed arguments and a local layout that fits, the emitted Core body
has a run from the standard call frame to the evaluated source word followed
by `return`. The run preserves the store for every profile and host relation. -/
theorem Func.toWasm_returns {H : Type} {params : List IntType} {result : IntType}
    (f : Func params result) (C : Context) (type : TypeIdx) (fits : f.Fits)
    (args : Env params) (m : ModuleInst) (P : Profile) (host : HostSemantics H) (s : Store H) :
    ∃ final, Steps P host
      ⟨s, Frame.forCall m args.toWasmArgs (f.toWasm C type fits).locals,
        expression (f.toWasm C type fits).body⟩
      ⟨s, final, vals [result.toVal (f.eval args)] ++ [.plain .return_]⟩ :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.toWasm_returns f C type fits args m P host s

/-- With the standard typed call frame, all Core executions of the emitted body
follow a finite deterministic path to the source word and `return`. -/
theorem Func.toWasm_body_completes {H : Type} {params : List IntType} {result : IntType}
    (f : Func params result) (C : Context) (type : TypeIdx) (fits : f.Fits)
    (args : Env params) (m : ModuleInst) (P : Profile) (host : HostSemantics H) (s : Store H) :
    ∃ final, CompletesAt P host
      ⟨s, Frame.forCall m args.toWasmArgs (f.toWasm C type fits).locals,
        expression (f.toWasm C type fits).body⟩
      ⟨s, final, vals [result.toVal (f.eval args)] ++ [.plain .return_]⟩ :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.toWasm_body_completes f C type fits args m P host s

/-- Every reachable Core `return` has exactly the source word on its stack,
with the original store and an empty instruction suffix. -/
theorem Func.toWasm_return_unique {H : Type} {P : Profile} {host : HostSemantics H}
    {params : List IntType} {result : IntType}
    (f : Func params result) (C : Context) (type : TypeIdx) (fits : f.Fits) (args : Env params)
    (m : ModuleInst) (s s' : Store H) (final : Frame) (stack : List Val) (rest : List Admin)
    (run : Steps P host
      ⟨s, Frame.forCall m args.toWasmArgs (f.toWasm C type fits).locals,
        expression (f.toWasm C type fits).body⟩
      ⟨s', final, vals stack ++ .plain .return_ :: rest⟩) :
    s' = s ∧ stack = [result.toVal (f.eval args)] ∧ rest = [] :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.toWasm_return_unique f C type fits args m s s' final stack rest run

/-- If the store holds an instance of the lowered code with the declared
signature, a Core invocation can finish with exactly the evaluated source word
and the original store. -/
theorem Func.toWasm_invoke {H : Type} {params : List IntType} {result : IntType}
    (f : Func params result) (C : Context) (type : TypeIdx) (fits : f.Fits) (args : Env params)
    (P : Profile) (host : HostSemantics H) (s : Store H) (addr : Nat) (fi : FuncInst H)
    (lookup : s.funcs[addr]? = some fi) (code : fi.code = .wasm (f.toWasm C type fits))
    (signature : Expand fi.type (Func.coreSignature params result)) :
    Steps P host (invoke s addr args.toWasmArgs) ⟨s, {}, vals [result.toVal (f.eval args)]⟩ :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.toWasm_invoke f C type fits args P host s addr fi lookup code signature

/-- With the emitted code installed at the stated address and signature, all
Core invocations follow a finite deterministic path to the source word. -/
theorem Func.toWasm_invoke_completes {H : Type} {params : List IntType} {result : IntType}
    (f : Func params result) (C : Context) (type : TypeIdx) (fits : f.Fits) (args : Env params)
    (P : Profile) (host : HostSemantics H) (s : Store H) (addr : Nat) (fi : FuncInst H)
    (lookup : s.funcs[addr]? = some fi) (code : fi.code = .wasm (f.toWasm C type fits))
    (signature : Expand fi.type (Func.coreSignature params result)) :
    CompletesAt P host (invoke s addr args.toWasmArgs) ⟨s, {}, vals [result.toVal (f.eval args)]⟩ :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.toWasm_invoke_completes f C type fits args P host s addr fi
    lookup code signature

end Silmaril.MLIR.WasmSSA
