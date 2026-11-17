module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAstLive

/-!
# Typed payloads and fixed arities through linear memory: soundness and non-vacuity

**Arities** (`witNode_admits`, `witWrite_admits`): every `node` call the decoder reads, hence
every decoded write, has a number of children admitted by its tag's arity.

**Bridges** (`witFixedLang_subset`, `witWriterLang_subset`): the generic role bridges at the
typed AST roles `witRoles S tagOf` and the writer `astW S.toAstSig`, for every WIT-typed
signature `S`.

**The example `calcMod`** (`node(0, 16, 0, 0)` over the `s64` `1` stored at `[16, 24)`, the same
over `2`, both handles stored at `[0, 8)`, `node(1, 0, 0, 2)`, `accept`), for every profile,
against every environment admitted by `hiReply`:

* `calcMod_fixed_sound`: in every fixed environment and for every policy without a sentinel, it
  accepts only `add(num 1, num 2)`;
* `calcMod_sound`: the same for the writer language (no sentinel, no undefined behaviour);
* `calcMod_live`: it accepts `add(num 1, num 2)`, for every policy (traced session against the
  counting host);
* `calcMod_lang`: **its writer language is exactly `{add(num 1, num 2)}`** (no sentinel, no
  undefined behaviour).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.IO Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Cons Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api

variable {S : WitSig} {tagOf : BitVec 32 → Option S.Tag} {P : Profile}
  {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat} {m : Module}

/-- **The decoder admits only the declared arities.** -/
theorem witNode_admits {o : Callout} {op : Σ t, S.toAstSig.Arg t} {hs : List (BitVec 32)}
    (h : Callout.witNode S tagOf o = some (op, hs)) : (S.arity op.1).Admits hs.length = true :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witNode_admits h

/-- **A decoded write has an admitted number of children.** -/
theorem witWrite_admits {ix : WitImports} {o : Callout} {w : HostReply}
    {op : Σ t, S.toAstSig.Arg t} {hs : List (BitVec 32)} {r : BitVec 32}
    (h : witWrite S tagOf ix o w = some (.write op hs r)) :
    (S.arity op.1).Admits hs.length = true :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witWrite_admits h

/-- **The typed AST writer bridge in a fixed environment**, for every policy. -/
theorem witFixedLang_subset {ix : WitImports} {pol : Policy (BitVec 32)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST S.toAstSig)} {L : Set (AST S.toAstSig)}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : MemSat P m memIdx (witRoles S tagOf ix)
      (roleWriterContract (witRoles S tagOf ix) (astW S.toAstSig) pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) :
    fixedLang (astW S.toAstSig) pol {ρ} (witTraces S tagOf P Envs memIdx m ix) ⊆ L :=
  rolesFixedLang_subset
    (fun _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witAccept_isAccept h)
    (fun _ _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witWrite_isWrite h)
    hsat hE

/-- **The typed AST writer bridge** (store semantics, no undefined behaviour). -/
theorem witWriterLang_subset {ix : WitImports} {pol : Policy (BitVec 32)}
    {L : Set (AST S.toAstSig)} {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (witRoles S tagOf ix)
      (roleWriterContract (witRoles S tagOf ix) (astW S.toAstSig) pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : witWriterLang S tagOf P Envs memIdx m ix pol ⊆ L :=
  rolesWriterLang_subset
    (fun _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witAccept_isAccept h)
    (fun _ _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witWrite_isWrite h)
    hsat hE hw ha

/-- **In a fixed environment, `calcMod` accepts only `add(num 1, num 2)`.** -/
theorem calcMod_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST calcSig.toAstSig)) :
    fixedLang (astW calcSig.toAstSig) pol {ρ}
      (witTraces calcSig calcTagOf P (ReplyEnvs hiReply) 0 calcMod {}) ⊆ {addTree} :=
  witFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.calc_sat P ρ)
    (fun _ _ h => h)

/-- **`calcMod` accepts only `add(num 1, num 2)`.** -/
theorem calcMod_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang calcSig calcTagOf P (ReplyEnvs hiReply) 0 calcMod {} pol ⊆ {addTree} :=
  witWriterLang_subset
    (fun ρ => by
      rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.calc_sat P ρ)
    (fun _ _ h => h) hw ha

/-- **`calcMod` accepts `add(num 1, num 2)`**, for every policy. -/
theorem calcMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    addTree ∈ witWriterLang calcSig calcTagOf P (ReplyEnvs hiReply) 0 calcMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitAst.calcMod_live P pol

/-- **The writer language of `calcMod` is exactly `{add(num 1, num 2)}`.** -/
theorem calcMod_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang calcSig calcTagOf P (ReplyEnvs hiReply) 0 calcMod {} pol = {addTree} :=
  Set.Subset.antisymm (calcMod_sound P hs hw ha)
    (Set.singleton_subset_iff.2 (calcMod_live P pol))

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
