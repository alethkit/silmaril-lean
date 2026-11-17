module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.KwText.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.KwTextLive

/-!
# The keyword text reader: soundness and non-vacuity

* `kwTextReaderLang_subset` (**the keyword text reader bridge**): with the keyword text reader
  contract proved in every fixed environment, the reader language under the trapping read policy
  is included in `L`, for every accept policy without undefined behaviour and every set of fixed
  environments.
* `kwTextMod_sound`: for every profile, against every host admitted by `itemsReply`,
  `kwTextMod` accepts only keywords whose UTF-8 text has two bytes (`twoByteKws`), by the
  Hoare-logic proof of `textMod` with the keyword decoder.
* `kwTextMod_live`: `kwTextMod` accepts the keyword `hi` in every set of fixed environments one
  of which names it (the session against `itemsEnv 0x6968 0`); `kwTextMod_bounds`: both bounds
  together. The language is not shown to be all of `twoByteKws` (the live session is for `hi`
  only).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.KwText

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms

/-- **The keyword text reader bridge.** -/
theorem kwTextReaderLang_subset {P : Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : KwTextImports} {L : Set SymStrKwBytesSExp}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (kwTextRoles ix) (kwTextContract ix ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrKwBytesSExp)) :
    kwTextReaderLang P Envs memIdx m ix .trap oa Rhos ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.KwText.kwTextReaderLang_subset hsat hE hoa
    Rhos

/-- **`kwTextMod` accepts only keywords of two UTF-8 bytes.** -/
theorem kwTextMod_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrKwBytesSExp)) :
    kwTextReaderLang P (ReplyEnvs itemsReply) 0 kwTextMod {} .trap oa Rhos ⊆ twoByteKws :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.KwText.kwTextMod_sound P hoa Rhos

/-- **`kwTextMod` accepts the keyword `hi`.** -/
theorem kwTextMod_live (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrKwBytesSExp)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrKwBytesSExp} (hρ : ρ ∈ Rhos)
    {h : BitVec 32} (e : ρ h = some (.atom kwAtom)) :
    .atom kwAtom ∈ kwTextReaderLang P (ReplyEnvs itemsReply) 0 kwTextMod {} .trap oa Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.KwText.kwTextMod_live P oa hρ e

/-- **Both bounds**: over every set of fixed environments naming the keyword `hi`, the language
of `kwTextMod` contains `hi` and consists of keywords of two UTF-8 bytes. -/
theorem kwTextMod_bounds (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrKwBytesSExp)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrKwBytesSExp} (hρ : ρ ∈ Rhos)
    {h : BitVec 32} (e : ρ h = some (.atom kwAtom)) :
    {.atom kwAtom} ⊆ kwTextReaderLang P (ReplyEnvs itemsReply) 0 kwTextMod {} .trap oa Rhos ∧
      kwTextReaderLang P (ReplyEnvs itemsReply) 0 kwTextMod {} .trap oa Rhos ⊆ twoByteKws :=
  ⟨Set.singleton_subset_iff.2 (kwTextMod_live P oa hρ e), kwTextMod_sound P hoa Rhos⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.KwText
