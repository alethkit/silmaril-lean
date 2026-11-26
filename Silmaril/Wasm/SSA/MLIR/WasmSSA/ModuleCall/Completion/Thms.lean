module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Execution.Defs
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Completion

/-! Composition of a certified internal direct call with a certified continuation. -/

public section

namespace Silmaril.MLIR.WasmSSA.ModuleCall

open Silmaril.Wasm (FuncIdx)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand Ty)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- A resolved direct call of a Wasm body with certified completion at `return`
resumes the certified caller continuation. The values below the arguments, the
caller frame, and the pending code are preserved until the callee returns. -/
theorem directCall_completes_then {s : Store H} {caller : Frame} {x : FuncIdx}
    {a : Nat} {fi : FuncInst H} {code : Wasm.Func} {ps rs : Ty (.list .val)}
    {below args results : List Val} {rest : List Admin} {finish : Config H}
    (index : caller.module.funcs[x.toNat]? = some a) (lookup : s.funcs[a]? = some fi)
    (stored : fi.code = .wasm code) (signature : Expand fi.type (.func ps rs))
    (arity : args.length = ps.length) (resultArity : results.length = rs.length)
    (body : ∃ final, CompletesAt P host
      ⟨s, Frame.forCall fi.module args code.locals, expression code.body⟩
      ⟨s, final, vals results ++ [.plain .return_]⟩)
    (then_ : CompletesAt P host ⟨s, caller, vals (below ++ results) ++ rest⟩ finish) :
    CompletesAt P host ⟨s, caller, vals (below ++ args) ++ .plain (.call x) :: rest⟩ finish :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.directCall_completes_then
    index lookup stored signature arity resultArity body then_

/-- The same return-shaped body certificate gives completion of Core invocation. -/
theorem invoke_completes_of_body {s : Store H} {a : Nat} {fi : FuncInst H} {code : Wasm.Func}
    {ps rs : Ty (.list .val)} {args results : List Val}
    (lookup : s.funcs[a]? = some fi) (stored : fi.code = .wasm code)
    (signature : Expand fi.type (.func ps rs)) (arity : args.length = ps.length)
    (resultArity : results.length = rs.length)
    (body : ∃ final, CompletesAt P host
      ⟨s, Frame.forCall fi.module args code.locals, expression code.body⟩
      ⟨s, final, vals results ++ [.plain .return_]⟩) :
    CompletesAt P host (invoke s a args) ⟨s, {}, vals results⟩ :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.invoke_completes_of_body
    lookup stored signature arity resultArity body

end Silmaril.MLIR.WasmSSA.ModuleCall
