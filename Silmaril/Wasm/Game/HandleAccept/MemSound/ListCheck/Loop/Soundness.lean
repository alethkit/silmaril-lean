module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Thms
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopModule

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Wasm.Game.HandleAccept.MemSound.Readers Silmaril.Accept.Handle Silmaril.Formats

/-- Every accepted tree is a list of symbols, across all permitted export calls and shaped replies. -/
theorem symbols_sound (profile : Profile) {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (mod {}) {} symTextAns .trap policy envs ⊆
      listsOf symbols :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound.symbols_sound profile noUB envs

/-- Every accepted tree is a list of blobs, across all permitted export calls and shaped replies. -/
theorem blobs_sound (profile : Profile) {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (mod blobImports) blobImports blobAns
      .trap policy envs ⊆ listsOf blobs :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound.blobs_sound profile noUB envs

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
