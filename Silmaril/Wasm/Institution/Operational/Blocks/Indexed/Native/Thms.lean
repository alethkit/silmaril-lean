module

public import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Indexed.Core
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Indexed.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Indexed.NativeCommon

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Indexed

open Execution
open Execution.Runtime (ModuleInst)
open SingleThreaded.Det (noHost)

/-- Numeric signatures in the current module instance transport through its
exact Core type-table embedding. Missing entries stay missing. -/
theorem core_type_idx (m : ModuleInst) (i : TypeIdx) :
    m.toCore.blockType? (.typeIdx i) =
      m.types[i.toNat]?.map (fun ft => (ft.params.map Validation.Ty.num, ft.results.map Validation.Ty.num)) :=
  Proofs.Core.type_idx m i

section Core

open Core

variable {H : Type} {P : Numerics.Profile} {s : Store H} {site : Site} {a : State} {dst : Config H}

theorem core_step_iff (ready : Admitted site a) :
    Step P noHost (coreConfig s site a) dst ↔
      ∃ out, Edge site a out ∧ dst = coreConfig s site out :=
  Proofs.Core.step_iff ready

theorem core_run_iff (ready : Admitted site a) :
    Relation.ReflTransGen (Step P noHost) (coreConfig s site a) dst ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ dst = coreConfig s site out :=
  Proofs.run_iff (coreConfig s site) _ (fun h => core_step_iff h) ready

end Core

section Lime1

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H} {site : Site} {a : State} {dst : Config H}

theorem lime_step_iff (ready : Admitted site a) :
    Step CallFrame.limeNoHost (limeConfig s site a) dst ↔
      ∃ out, Edge site a out ∧ dst = limeConfig s site out :=
  Proofs.Lime1.step_iff ready

theorem lime_run_iff (ready : Admitted site a) :
    Relation.ReflTransGen (Step CallFrame.limeNoHost) (limeConfig s site a) dst ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ dst = limeConfig s site out :=
  Proofs.run_iff (limeConfig s site) _ (fun h => lime_step_iff h) ready

end Lime1

end Silmaril.Wasm.Institution.Operational.Blocks.Indexed
