module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints

open Silmaril.Wasm.Component.Runtime

/-- Spending a claim does not remove an accepted tree or leave a copy of the claim. -/
theorem spend_preserves_observations {sig : Signature} {state updated : State sig} {id : EndId}
    (spent : state.spend id = .ok updated) : updated.accepted = state.accepted ∧ id ∉ updated.held := by
  unfold State.spend at spent
  split at spent <;> cases spent
  simp

/-- A retained observation does not make a spent claim spendable again. -/
theorem spend_no_second_give {sig : Signature} {state updated : State sig} {id : EndId}
    (spent : state.spend id = .ok updated) : updated.spend id = .error .unclaimed := by
  simp [State.spend, (spend_preserves_observations spent).2]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
