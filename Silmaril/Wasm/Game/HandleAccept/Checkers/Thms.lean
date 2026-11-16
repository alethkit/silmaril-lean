module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs
public import Silmaril.Wasm.Game.HandleAccept.Thms

/-!
# Executable reader checkers: what is proved

* The three modules validate and instantiate (`properCheck_instance`, …, by kernel evaluation of
  `Silmaril.Wasm.Verify.instance?`), with the five cons imports in order.
* `sortedL ⊆ wordsL ⊆ properL` (the subset theorems of the languages).
* **Conditional soundness**: each checker's reader language under the trapping read policy, in
  every environment and for every profile, is included in its language *given* its open
  Hoare-logic obligation `Task.…Sat` (`properCheck_sound_of`, …), through
  `consLang_sound_of_forall` and `Silmaril.Wasm.Logic.GameLink.strategy_sound`. The obligations
  themselves are **not proved** here.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Formats Silmaril.Accept.Handle

theorem properCheck_instance : (Verify.instance? properCheck).isSome = true := by decide +kernel
theorem wordsCheck_instance : (Verify.instance? wordsCheck).isSome = true := by decide +kernel
theorem sortedCheck_instance : (Verify.instance? sortedCheck).isSome = true := by decide +kernel

theorem properCheck_imports :
    (Verify.instOf properCheck).imports.length = 5 := by decide +kernel

theorem ofAtoms_properList (ws : List (BitVec 64)) : SExp2.ProperList (SExp2.ofAtoms ws) := by
  apply SExp2.properList_ofList
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact .inl (.atom w)

theorem sortedL_subset_wordsL : sortedL ⊆ wordsL := fun _ ⟨ws, h, _⟩ => ⟨ws, h⟩

theorem wordsL_subset_properL : wordsL ⊆ properL := by
  rintro _ ⟨ws, rfl⟩
  exact ofAtoms_properList ws

theorem properCheck_sound_of (h : Task.properCheckSat) (P : Profile)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsLang P properCheck consIx .trap .trap Envs ⊆ properL :=
  consLang_sound_of_forall (fun ρ _ => h P ρ) trivial (by decide)

theorem wordsCheck_sound_of (h : Task.wordsCheckSat) (P : Profile)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsLang P wordsCheck consIx .trap .trap Envs ⊆ wordsL :=
  consLang_sound_of_forall (fun ρ _ => h P ρ) trivial (by decide)

theorem sortedCheck_sound_of (h : Task.sortedCheckSat) (P : Profile)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsLang P sortedCheck consIx .trap .trap Envs ⊆ sortedL :=
  consLang_sound_of_forall (fun ρ _ => h P ρ) trivial (by decide)

end Silmaril.Wasm.Game.HandleAccept.Checkers
