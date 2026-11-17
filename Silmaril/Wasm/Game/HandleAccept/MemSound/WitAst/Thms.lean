module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAstLive
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAppLive

/-!
# Typed payloads and fixed arities through linear memory: soundness and non-vacuity

**Payloads** (`readPtrLen_encode`, `readVal_rest`, `readVal_string`, `readVal_bytes`,
`readVal_list`): a `(ptr, len)` pair written as two little-endian `i32`s is read back; every
payload value consumes exactly `PTy.width t` bytes of the payload area; strings, byte strings and
lists are read through their pair from the memory at the call. Kernel-checked examples over the
memory `exMem` (`listSeg`): `ex_string`, `ex_string_utf8` (two-byte UTF-8), `ex_bytes`,
`ex_list_u32`, `ex_list_string` (a list of strings: two levels of indirection), `ex_vals`
(`u32` then `string`, packed), and the failures `ex_bad_utf8`, `ex_out_of_bounds`,
`ex_unconsumed` (a payload area longer than its vector).

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

**The example `appMod`** (string payloads: `"f"` stored at `[24, 25)` and the pair `(24, 1)` at
`[16, 24)` right before `node(0, 16, 0, 0)`, the same with `"x"`, both handles at `[0, 8)`,
`node(1, 0, 0, 2)`, `accept`), for every profile, against every environment admitted by
`hiReply`: `appMod_fixed_sound`, `appMod_sound` (Hoare proof `app_sat`), `appMod_live` (traced
session against the counting host), `appMod_lang`: **its writer language is exactly
`{app(var "f", var "x")}`** (no sentinel, no undefined behaviour).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.IO Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Cons Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api

/-! ## Payloads -/

/-- **A `(ptr, len)` pair is read back.** -/
theorem readPtrLen_encode (p n : BitVec 32) (rest : List UInt8) :
    readPtrLen ((Execution.Memory.encodeLE 4 p.toNat).data.toList ++
      (Execution.Memory.encodeLE 4 n.toNat).data.toList
      ++ rest) = some (p.toNat, n.toNat, rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readPtrLen_encode p n rest

/-- **A payload value consumes exactly its width** of the payload area. -/
theorem readVal_rest {seg : Nat → Nat → Option (List UInt8)} {t : PTy} {bs rest : List UInt8}
    {v : t.Val} (h : readVal seg t bs = some (v, rest)) : rest = bs.drop (PTy.width t) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_rest h

/-- **A string payload**: its pair, the segment it names, the UTF-8 text. -/
theorem readVal_string {seg : Nat → Nat → Option (List UInt8)} {bs rest cs : List UInt8}
    {p n : Nat} {str : String} (hp : readPtrLen bs = some (p, n, rest))
    (hc : seg p n = some cs) (hu : Memory.utf8? cs = some str) :
    readVal seg .string bs = some (str, rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_string hp hc hu

/-- **A byte-string payload**: its pair and the segment it names. -/
theorem readVal_bytes {seg : Nat → Nat → Option (List UInt8)} {bs rest cs : List UInt8}
    {p n : Nat} (hp : readPtrLen bs = some (p, n, rest)) (hc : seg p n = some cs) :
    readVal seg .bytes bs = some (cs, rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_bytes hp hc

/-- **A list payload**: its pair, the segment of `len` packed elements, the elements. -/
theorem readVal_list {seg : Nat → Nat → Option (List UInt8)} {t : PTy}
    {bs rest es : List UInt8} {p n : Nat} {vs : List t.Val}
    (hp : readPtrLen bs = some (p, n, rest)) (hc : seg p (n * PTy.width t) = some es)
    (hm : readMany (readVal seg t) n es = some (vs, [])) :
    readVal seg (.list t) bs = some (vs, rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_list hp hc hm

/-- The string `"hi"` through the pair `(8, 2)`. -/
theorem ex_string : readVal (listSeg exMem) .string [8, 0, 0, 0, 2, 0, 0, 0] =
    some ("hi", []) := by kernel_rfl

/-- A two-byte UTF-8 character: `"é"` through `(10, 2)`. -/
theorem ex_string_utf8 : readVal (listSeg exMem) .string [10, 0, 0, 0, 2, 0, 0, 0] =
    some ("é", []) := by kernel_rfl

/-- The same pair as a byte string. -/
theorem ex_bytes : readVal (listSeg exMem) .bytes [10, 0, 0, 0, 2, 0, 0, 0] =
    some (([0xC3, 0xA9] : List UInt8), []) := by kernel_rfl

/-- A `list<u32>` of two elements at `12`. -/
theorem ex_list_u32 : readVal (listSeg exMem) (.list .u32) [12, 0, 0, 0, 2, 0, 0, 0] =
    some (([7, 9] : List UInt32), []) := by kernel_rfl

/-- A `list<string>`: two pairs at `20`, each naming a string. -/
theorem ex_list_string : readVal (listSeg exMem) (.list .string) [20, 0, 0, 0, 2, 0, 0, 0] =
    some ((["hi", "é"] : List String), []) := by kernel_rfl

/-- A payload vector `(u32, string)`, packed: twelve bytes. -/
theorem ex_vals : readVals (listSeg exMem) [.u32, .string]
    [5, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0] = some ((5 : UInt32), "hi", ()) := by kernel_rfl

/-- Invalid UTF-8 is no string. -/
theorem ex_bad_utf8 : readVal (listSeg exMem) .string [36, 0, 0, 0, 1, 0, 0, 0] = none := by
  kernel_rfl

/-- A segment out of bounds is no value. -/
theorem ex_out_of_bounds : readVal (listSeg exMem) .bytes [36, 0, 0, 0, 2, 0, 0, 0] = none := by
  kernel_rfl

/-- A payload area longer than its vector is rejected. -/
theorem ex_unconsumed : readVals (listSeg exMem) [.string] [8, 0, 0, 0, 2, 0, 0, 0, 0] = none := by
  kernel_rfl

/-! ## Arities and bridges -/

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

/-! ## String payloads: `appMod` -/

/-- **In a fixed environment, `appMod` accepts only `app(var "f", var "x")`.** -/
theorem appMod_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST appSig.toAstSig)) :
    fixedLang (astW appSig.toAstSig) pol {ρ}
      (witTraces appSig appTagOf P (ReplyEnvs hiReply) 0 appMod {}) ⊆ {appTree} :=
  witFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitApp.app_sat P ρ)
    (fun _ _ h => h)

/-- **`appMod` accepts only `app(var "f", var "x")`.** -/
theorem appMod_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang appSig appTagOf P (ReplyEnvs hiReply) 0 appMod {} pol ⊆ {appTree} :=
  witWriterLang_subset
    (fun ρ => by
      rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitApp.app_sat P ρ)
    (fun _ _ h => h) hw ha

/-- **`appMod` accepts `app(var "f", var "x")`**, for every policy. -/
theorem appMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    appTree ∈ witWriterLang appSig appTagOf P (ReplyEnvs hiReply) 0 appMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitApp.appMod_live P pol

/-- **The writer language of `appMod` is exactly `{app(var "f", var "x")}`.** -/
theorem appMod_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang appSig appTagOf P (ReplyEnvs hiReply) 0 appMod {} pol = {appTree} :=
  Set.Subset.antisymm (appMod_sound P hs hw ha)
    (Set.singleton_subset_iff.2 (appMod_live P pol))

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
