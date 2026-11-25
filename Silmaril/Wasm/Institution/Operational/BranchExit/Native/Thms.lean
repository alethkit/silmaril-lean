module

public import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Defs
public import Silmaril.Wasm.Institution.Operational.BranchExit.Thms
public import Silmaril.Wasm.Execution.Core.Step
import Silmaril.Proofs.Wasm.Institution.Operational.BranchExit.V1
import Silmaril.Proofs.Wasm.Institution.Operational.BranchExit.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.BranchExit.Core
import Silmaril.Proofs.Wasm.Institution.Operational.BranchExit.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.BranchExit

open Execution
open Execution.Runtime (Frame)

section v1
variable {H : Type} {host : Wasm.V1.Execution.HostSemantics H}
  {s : Wasm.V1.Execution.Store H} {f : Frame} {ty : Option NumType}

theorem v1_sound {a b : State} (edge : Edge ty a b) :
    Wasm.V1.Execution.Step host (v1Config s f ty a) (v1Config s f ty b) :=
  Proofs.V1.sound edge

theorem v1_step_iff {a : State} {b : Wasm.V1.Execution.Config H} (guard : Admitted ty a) :
    Wasm.V1.Execution.Step host (v1Config s f ty a) b ↔
      ∃ out, Edge ty a out ∧ b = v1Config s f ty out :=
  ⟨Proofs.V1.readback guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound edge⟩

theorem v1_run_iff {a : State} {b : Wasm.V1.Execution.Config H} (guard : Admitted ty a) :
    Relation.ReflTransGen (Wasm.V1.Execution.Step host) (v1Config s f ty a) b ↔
      ∃ out, Runs ty a out ∧ Admitted ty out ∧ b = v1Config s f ty out :=
  Proofs.run_iff (v1Config s f ty) _ (fun e => v1_sound e)
    (fun ready step => (v1_step_iff ready).mp step) guard

end v1

section lime
variable {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
  {s : Wasm.Lime1.Execution.Store H} {f : Frame} {ty : Option NumType}

theorem lime_sound {a b : State} (edge : Edge ty a b) :
    Wasm.Lime1.Execution.Step host (limeConfig s f ty a) (limeConfig s f ty b) :=
  Proofs.Lime1.sound edge

theorem lime_step_iff {a : State} {b : Wasm.Lime1.Execution.Config H} (guard : Admitted ty a) :
    Wasm.Lime1.Execution.Step host (limeConfig s f ty a) b ↔
      ∃ out, Edge ty a out ∧ b = limeConfig s f ty out :=
  ⟨Proofs.Lime1.readback guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound edge⟩

theorem lime_run_iff {a : State} {b : Wasm.Lime1.Execution.Config H} (guard : Admitted ty a) :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step host) (limeConfig s f ty a) b ↔
      ∃ out, Runs ty a out ∧ Admitted ty out ∧ b = limeConfig s f ty out :=
  Proofs.run_iff (limeConfig s f ty) _ (fun e => lime_sound e)
    (fun ready step => (lime_step_iff ready).mp step) guard

end lime

section core
variable {H : Type} {P : Numerics.Profile} {host : Core.HostSemantics H}
  {s : Core.Store H} {f : Core.Frame} {ty : Option NumType}

theorem core_sound {a b : State} (edge : Edge ty a b) :
    Core.Step P host (coreConfig s f ty a) (coreConfig s f ty b) :=
  Proofs.core_sound edge

theorem core_step_iff {a : State} {b : Core.Config H} (guard : Admitted ty a) :
    Core.Step P host (coreConfig s f ty a) b ↔
      ∃ out, Edge ty a out ∧ b = coreConfig s f ty out :=
  ⟨Proofs.core_readback guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound edge⟩

theorem core_run_iff {a : State} {b : Core.Config H} (guard : Admitted ty a) :
    Relation.ReflTransGen (Core.Step P host) (coreConfig s f ty a) b ↔
      ∃ out, Runs ty a out ∧ Admitted ty out ∧ b = coreConfig s f ty out :=
  Proofs.run_iff (coreConfig s f ty) _ (fun e => core_sound e)
    (fun ready step => (core_step_iff ready).mp step) guard

end core

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame)
    (ty : Option NumType) (a : State) :
    (v1Config s f ty a).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) f ty a :=
  Proofs.v1_to_lime s f ty a

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame)
    (ty : Option NumType) (a : State) :
    (limeConfig s f ty a).toCore = coreConfig s.toCore f.toCore ty a :=
  Proofs.lime_to_core s f ty a

end Silmaril.Wasm.Institution.Operational.BranchExit
