module

public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Execution.Core

variable {grow : SingleThreaded.GrowOracle} {Host : Type}

/-- The local obligation at a reached arbitrary `modify` operation. Engine steps,
scheduler bookkeeping and traps do not need an update certificate. The dispatcher
and raw host programs may install new programs; their updates are checked when run. -/
def CoreUpdateGrows (config : Config (core3 grow) Host) : Prop :=
  match config.ctl with
  | ⟨_, .prog (.op (.modify update) _), _⟩ :: _ =>
    Core3.Grows config.store.core (update config.store).core
  | _ => True

/-- An actual scheduler prefix with evidence for just the reached `modify` operations.
This is not a restriction on guest Core memory writes, and includes trapping prefixes. -/
inductive CoreGrowthSteps (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))) :
    Config (core3 grow) Host → List (Label (core3 grow) Host) → Config (core3 grow) Host → Prop where
  | refl (config : Config (core3 grow) Host) : CoreGrowthSteps profile ready dispatch config [] config
  | cons {before current after label trace} :
    CoreUpdateGrows before → Step profile ready dispatch before label current →
    CoreGrowthSteps profile ready dispatch current trace after →
    CoreGrowthSteps profile ready dispatch before (label :: trace) after

end Silmaril.Wasm.Component.Machine
