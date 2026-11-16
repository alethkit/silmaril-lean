module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecFull.Defs
public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecProper.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull.Sat

/-!
# The full recursive-properness checker: what is proved

* `recFullCheck` validates and instantiates (`recFullCheck_instance`).
* **Hoare-logic specification** (`recFullCheck_sat`): in every environment `ρ` and every
  profile, the instance meets the cons reader specification `consISpec consIx ρ recProperL`
  with the store invariant `consInv`. The exported function calls itself; the proof (in
  `Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull`) gives the internal call the
  specification "if it returns normally, the argument denotes a recursively proper list" and
  proves it for arguments of every size by induction on the size, the recursive calls being on
  strictly smaller elements.
* **Soundness**: under the trapping read policy and every accept policy but `ub`, in every set
  of environments and every profile, the checker accepts only recursively proper lists
  (`recFullCheck_sound`), at every nesting depth, unlike the depth-two `recProperCheck`.
* `(((1)))` (`deep1`) is recursively proper (`deep1_mem_recProperL'`) and rejected by every run
  of `recProperCheck` (`recProperCheck_rejects_deep1`); `Examples` shows `recFullCheck` accepts
  it.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Formats Silmaril.Accept.Handle

theorem recFullCheck_instance : (Verify.instance? recFullCheck).isSome = true := by
  decide +kernel

theorem deep1_mem_recProperL' : deep1 ∈ recProperL := deep1_mem_recProperL

/-- **`recFullCheck` meets the cons reader specification of `recProperL`.** -/
theorem recFullCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P
    (Verify.instOf recFullCheck) (consInv recFullCheck) (consISpec consIx ρ recProperL)
    (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull.recFullCheck_sat

/-- **`recFullCheck` accepts only recursively proper lists**, at every depth. -/
theorem recFullCheck_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsLang P recFullCheck consIx .trap oa Envs ⊆ recProperL :=
  consLang_sound_of_forall (fun ρ _ => recFullCheck_sat P ρ) rfl hoa

/-- **`recFullCheck` rejects `dottedElem`** in every environment and profile. -/
theorem recFullCheck_rejects_dottedElem (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    dottedElem ∉ moduleConsLang P recFullCheck consIx .trap oa Envs :=
  fun h => dottedElem_not_mem_recProperL (recFullCheck_sound P hoa Envs h)

/-- **`recProperCheck` rejects `(((1)))`**: it is nested three deep. -/
theorem recProperCheck_rejects_deep1 (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    deep1 ∉ moduleConsLang P recProperCheck consIx .trap oa Envs :=
  fun h => deep1_not_mem_nestL (recProperCheck_sound P hoa Envs h)

end Silmaril.Wasm.Game.HandleAccept.Checkers
