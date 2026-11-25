module

public import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
public import Silmaril.Wasm.Institution.Operational.Blocks.Native.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.Loops.Native

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Loops

open Execution.Runtime (Value)
open CallContinuation

section Core

open Execution.Core
open Wasm.SingleThreaded.Det (noHost)

/-- Entry installs a restart label with the resolved parameter arity. -/
theorem core_loop_step_iff {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame}
    {bt : BlockType} {body : List Instr} {stack : List Val} {rest : List Admin} {dst : Config H} :
    Step P noHost ⟨s, f, vals stack ++ .plain (.loop bt body) :: rest⟩ dst ↔
      ∃ (saved args : List Val) (params results : List Wasm.Validation.CValType),
        stack = saved ++ args ∧ f.module.blockType? bt = some (params, results) ∧
        args.length = params.length ∧
        dst = ⟨s, f, vals saved ++ .label params.length [.loop bt body] (vals args ++ expression body) :: rest⟩ :=
  Proofs.core_loop_step_iff

/-- Entry saves the outside operands and installs a restart continuation with arity zero. -/
theorem core_entry_iff {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame} {result : Option NumType}
    {saved : List Val} {body : List Instr} {rest : List Admin} {dst : Config H} :
    Step P noHost ⟨s, f, vals saved ++ .plain (.loop (Blocks.coreType result) body) :: rest⟩ dst ↔
      dst = ⟨s, f, vals saved ++ .label 0 [.loop (Blocks.coreType result) body] (expression body) :: rest⟩ :=
  Proofs.core_entry_iff

/-- A depth-zero branch drops the iteration operands and pending code.
Executing the reinstated loop instruction is a separate step. -/
theorem core_restart_iff {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame} {cont : List Instr}
    {saved scratch : List Val} {pending rest : List Admin} {dst : Config H} :
    Step P noHost
      ⟨s, f, vals saved ++ .label 0 cont (vals scratch ++ .plain (.br ⟨0⟩) :: pending) :: rest⟩ dst ↔
      dst = ⟨s, f, vals saved ++ expression cont ++ rest⟩ :=
  Proofs.core_restart_iff

/-- Values or a final trap exit the label without running its restart continuation. -/
theorem core_result_iff {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame} {cont : List Instr}
    {saved : List Val} {r : Nested.Result} {rest : List Admin} {dst : Config H} :
    let code := Nested.resultCode Blocks.Context.coreValues .trap r
    Step P noHost ⟨s, f, vals saved ++ .label 0 cont code :: rest⟩ dst ↔
      dst = ⟨s, f, vals saved ++ code ++ rest⟩ :=
  Proofs.core_result_iff

end Core

section Lime

open Wasm.Lime1.Execution
open Execution.Runtime (Frame)

/-- Entry saves the outside operands and installs a restart continuation with arity zero. -/
theorem lime_entry_iff {H : Type} {s : Store H} {f : Frame} {result : Option NumType}
    {saved : List Value} {body : Wasm.Lime1.Expr} {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values saved ++ .source (.loop (Blocks.limeType result) body) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ .label 0 [.loop (Blocks.limeType result) body] (expression body) :: rest⟩ :=
  Proofs.lime_entry_iff

/-- A depth-zero branch drops the iteration operands and pending code.
Executing the reinstated loop instruction is a separate step. -/
theorem lime_restart_iff {H : Type} {s : Store H} {f : Frame} {cont : Wasm.Lime1.Expr}
    {saved scratch : List Value} {pending rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost
      ⟨s, f, values saved ++ .label 0 cont (values scratch ++ .source (.br ⟨0⟩) :: pending) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ expression cont ++ rest⟩ :=
  Proofs.lime_restart_iff

/-- Values or a final trap exit the label without running its restart continuation. -/
theorem lime_result_iff {H : Type} {s : Store H} {f : Frame} {cont : Wasm.Lime1.Expr}
    {saved : List Value} {r : Nested.Result} {rest : List Admin} {dst : Config H} :
    let code := Nested.resultCode values .trap r
    Step CallFrame.limeNoHost ⟨s, f, values saved ++ .label 0 cont code :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ code ++ rest⟩ :=
  Proofs.lime_result_iff

end Lime

section V1

open Wasm.V1.Execution
open Execution.Runtime (Frame)

/-- Entry saves the outside operands and installs a restart continuation with arity zero. -/
theorem v1_entry_iff {H : Type} {s : Store H} {f : Frame} {result : Option NumType}
    {saved : List Value} {body : Wasm.V1.Expr} {rest : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost ⟨s, f, values saved ++ .source (.loop result body) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ .label 0 [.loop result body] (expression body) :: rest⟩ :=
  Proofs.v1_entry_iff

/-- A depth-zero branch drops the iteration operands and pending code.
Executing the reinstated loop instruction is a separate step. -/
theorem v1_restart_iff {H : Type} {s : Store H} {f : Frame} {cont : Wasm.V1.Expr}
    {saved scratch : List Value} {pending rest : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost
      ⟨s, f, values saved ++ .label 0 cont (values scratch ++ .source (.br ⟨0⟩) :: pending) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ expression cont ++ rest⟩ :=
  Proofs.v1_restart_iff

/-- Values or a final trap exit the label without running its restart continuation. -/
theorem v1_result_iff {H : Type} {s : Store H} {f : Frame} {cont : Wasm.V1.Expr}
    {saved : List Value} {r : Nested.Result} {rest : List Admin} {dst : Config H} :
    let code := Nested.resultCode values .trap r
    Step CallFrame.v1NoHost ⟨s, f, values saved ++ .label 0 cont code :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ code ++ rest⟩ :=
  Proofs.v1_result_iff

end V1

end Silmaril.Wasm.Institution.Operational.Loops
