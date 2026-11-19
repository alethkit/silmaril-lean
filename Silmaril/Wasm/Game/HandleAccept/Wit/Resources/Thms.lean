module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Resources.Defs
import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Resources

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

/-- Erasing the owning identity gives exactly the legacy reference lift, including
the removal-first failure behavior. -/
theorem take_representation {E : CoreEngine} {World : Type} (limits : Component.Limits)
    (cx : LiftLowerContext E) (resource : RtId) (slot : Nat) :
    (take (World := World) limits cx resource slot).bind
      (fun owner => Prog.pure (Owned.representation (resource := resource) owner)) =
      liftOwn limits cx resource slot :=
  liftOwnWith_map limits cx resource slot _ _

end Silmaril.Wasm.Game.HandleAccept.Wit.Resources
