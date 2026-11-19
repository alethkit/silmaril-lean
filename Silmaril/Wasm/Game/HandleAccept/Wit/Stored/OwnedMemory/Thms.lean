module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Project

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm (AddrType)

/-- Erasing the witnesses for the moved owners recovers the whole canonical
memory-lift program, including its effects and traps in their original order. -/
theorem project {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (type : TypeOf) (ptr : Nat) :
    Observed.value <$> loadAtWith limits cx width (carrier (World := World) limits quirks cx) type ptr =
      loadAt limits quirks cx width type ptr :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.project limits quirks cx width type ptr

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
