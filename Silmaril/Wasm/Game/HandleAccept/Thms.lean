module

public import Silmaril.Wasm.Game.HandleAccept.Defs
public import Silmaril.Wasm.Logic.GameLink.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Basic

/-!
# Handle-based tree acceptance of core Wasm modules: laws

* `readerLang_subset_of_AG` (generic): if every play of a strategy is assume/guarantee correct
  for an import specification whose answers are the correct reads in a fixed environment `ρ`
  and whose `accept` calls name members of `L`, then its reader language in `ρ` under the
  trapping read policy is included in `L`. Reads are per-move facts, so no history is needed.
* `consLang_sound_of_gameSat`: for a module using the cons reader API, the Hoare-logic
  obligation `GameSat P (instOf m) Inv (consISpec ix ρ L) (topISpec _)` (with a store invariant
  holding initially) gives `moduleConsLang P m ix .trap oa {ρ} ⊆ L`, through
  `Silmaril.Wasm.Logic.GameLink.strategy_sound`; `consLang_sound_of_forall` for every
  environment of a set.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Logic.Strategy (ISpec AG MoveGood agStrat)
open Silmaril.Wasm.Logic.GameLink (GameSat)

variable {E F : Sig.{0}}

theorem readerLang_subset_of_AG {Q A H X : Type} {R : Reader Q A H X} {ρ : Silmaril.Accept.Handle.Env H X} {L : Set X}
    {σ : Strategy E F} {decAsk : E.Op → Option (REv Q A H)}
    {decAns : (e : E.Op) → E.Ar e → Option (REv Q A H)} {Ii : ISpec E}
    (hAG : ∀ p ∈ σ, AG Ii (topISpec F) p)
    (hpost : ∀ e v, (∀ q a, decAns e v = some (.read q a) → R.valid ρ q ∧ R.ok ρ q a) →
      Ii.post e v)
    (hpre : ∀ e h, decAsk e = some (.accept h) → Ii.pre e → ∀ t, ρ h = some t → t ∈ L)
    (hans : ∀ e v h, decAns e v ≠ some (.accept h)) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    readerLang R .trap oa {ρ} (handleTraces σ decAsk decAns) ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.readerLang_subset_of_AG hAG hpost hpre hans hoa

theorem consDecAns_ne_accept {ts : List FnType} (ix : ConsImports) (e : (ifaceSig ts).Op)
    (v : (ifaceSig ts).Ar e) (h : BitVec 32) : consDecAns ix e v ≠ some (.accept h) := by
  intro hd
  unfold consDecAns at hd
  rcases h1 : i32Arg e.2.1 with _ | k <;> rcases h2 : ansVals v with _ | vs <;>
    simp only [h1, h2, Option.bind_eq_bind, Option.bind_none, Option.bind_some] at hd
  · cases hd
  · cases hd
  · cases hd
  · split_ifs at hd <;> revert hd <;> cases i32Res vs <;> cases i64Res vs <;> simp

/-- **Soundness of a cons reader checker from its Hoare-logic obligation.** -/
theorem consLang_sound_of_gameSat {P : Profile} {m : Module} {ix : ConsImports}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}
    {Inv : Store Nat → Prop}
    (hm : GameSat P (Verify.instOf m) Inv (consISpec ix ρ L) (topISpec _))
    (hs : Inv (Verify.instOf m).store) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    moduleConsLang P m ix .trap oa {ρ} ⊆ L :=
  readerLang_subset_of_AG
    (fun p hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound hm hs hp).2)
    (fun _ _ h => h) (fun _ h hd hpre => hpre h hd)
    (consDecAns_ne_accept ix) hoa

/-- For every environment of a set. -/
theorem consLang_sound_of_forall {P : Profile} {m : Module} {ix : ConsImports}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))} {L : Set (SExp2 (BitVec 64))}
    {Inv : Store Nat → Prop}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv (consISpec ix ρ L) (topISpec _))
    (hs : Inv (Verify.instOf m).store) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    moduleConsLang P m ix .trap oa Envs ⊆ L := by
  intro x hx
  unfold moduleConsLang readerLang langOver at hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨⟨ρ, hρ⟩, hx⟩ := hx
  refine consLang_sound_of_gameSat (hm ρ hρ) hs hoa ?_
  unfold moduleConsLang readerLang langOver
  rw [Set.mem_iUnion]
  exact ⟨⟨ρ, rfl⟩, hx⟩

end Silmaril.Wasm.Game.HandleAccept
