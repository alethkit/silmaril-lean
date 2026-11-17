module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Ast.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom.Defs

/-!
# Typed payloads and fixed arities through linear memory: `node(tag, payload, children, n)`

`Silmaril.Wasm.Game.HandleAccept.MemSound.Ast` reads string tags without payloads, any number of
children (`strSig`, `Arity.star`). For a **WIT-typed signature** `S : WitSig` (payload types
`S.params t`, arities `S.arity t`) with tags numbered by `tagOf : BitVec 32 → Option S.Tag`:

* `PTy.width`, `readVal`, `readVals`: scalar payloads (`bool`: one byte, `s32`/`u32`: four,
  `s64`/`u64`: eight, all little-endian) packed one after the other; strings, byte strings and
  lists are not read (`readVal` fails on them);
* `Callout.witNode S tagOf`: the call `node(tag, payload, children, n)` names the tag `tagOf tag`,
  reads its payload vector from the `valsWidth (S.params t)` bytes at `payload` and `n`
  little-endian `i32` child handles at `[children, children + 4n)` of the memory at the call,
  and **admits only the declared arity**: the number of children must be admitted by
  `S.arity t` (otherwise, as out of bounds, no event);
* `witWrite`, `witAccept`, `witRoles`, `witTraces`, `witWriterLang`: the write at the answer of a
  call returning one `i32` handle, `accept(h)` at the call, and the writer language over
  `astW S.toAstSig`.

## The example `calcMod`

The signature `calcSig`: tags `num` (tag `0`, one `s64` payload, no children) and `add` (tag `1`,
no payload, **exactly two** children). Imports `0 wit.node : [i32 i32 i32 i32] → [i32]`,
`1 wit.accept : [i32] → []`; one memory page; export `run : [] → []` with two `i32` locals:

```wat
(func $run (local $a i32) (local $b i32)
  (i64.store (i32.const 16) (i64.const 1))                         ;; payload 1 at [16, 24)
  (local.set $a (call $node (i32.const 0) (i32.const 16) (i32.const 0) (i32.const 0)))
  (i64.store (i32.const 16) (i64.const 2))                         ;; payload 2 at [16, 24)
  (local.set $b (call $node (i32.const 0) (i32.const 16) (i32.const 0) (i32.const 0)))
  (i32.store (i32.const 0) (local.get $a))                         ;; children [$a $b] at 0
  (i32.store (i32.const 4) (local.get $b))
  (call $accept (call $node (i32.const 1) (i32.const 0) (i32.const 0) (i32.const 2))))
```

It builds `add(num 1, num 2)` (`addTree`). Every payload and child list is written right before
the call that reads it, since an answer may rewrite memory. The admitted hosts are those of
`hiMod` (`hiReply`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom

/-! ## Scalar payloads in memory -/

/-- The bytes of a scalar payload type in memory (`0`: not read). -/
def PTy.width : PTy → Nat
  | .bool => 1
  | .s32 | .u32 => 4
  | .s64 | .u64 => 8
  | _ => 0

/-- The bytes of a payload vector. -/
def valsWidth (ps : List PTy) : Nat := (ps.map PTy.width).sum

/-- A little-endian `i32` (exactly four bytes). -/
def le32 (bs : List UInt8) : Option (BitVec 32) :=
  match le32s bs with
  | some [v] => some v
  | _ => none

/-- **One scalar payload value** at the head of `bs`, and the rest. -/
def readVal : (t : PTy) → List UInt8 → Option (t.Val × List UInt8)
  | .bool, b :: bs => some (b != 0, bs)
  | .s32, bs => (le32 (bs.take 4)).map fun v => (Int32.ofBitVec v, bs.drop 4)
  | .u32, bs => (le32 (bs.take 4)).map fun v => (UInt32.ofBitVec v, bs.drop 4)
  | .s64, bs => (le64 (bs.take 8)).map fun v => (Int64.ofBitVec v, bs.drop 8)
  | .u64, bs => (le64 (bs.take 8)).map fun v => (UInt64.ofBitVec v, bs.drop 8)
  | _, _ => none

/-- **A payload vector**, packed: every byte is consumed. -/
def readVals : (ps : List PTy) → List UInt8 → Option (PTy.Vals ps)
  | [], [] => some ()
  | [], _ :: _ => none
  | t :: ps, bs => (readVal t bs).bind fun (v, rest) => (readVals ps rest).map fun vs => (v, vs)

/-! ## The signature and the decoder -/

variable (S : WitSig) (tagOf : BitVec 32 → Option S.Tag)

/-- Writer events of the tagged-AST writer of `S`. -/
abbrev WitWEv := WEv (Σ t, S.toAstSig.Arg t) (BitVec 32)

/-- The named imports of the typed AST writer through memory. -/
structure WitImports where
  node : String × String := ("wit", "node")
  accept : String × String := ("wit", "accept")

/-- **`node(tag, payload, children, n)`**: the tag `tagOf tag` with its payload vector at
`payload` and the `n` little-endian child handles at `[children, children + 4n)`, when the tag
admits that many children. -/
def Callout.witNode (o : Callout) : Option ((Σ t, S.toAstSig.Arg t) × List (BitVec 32)) :=
  match o.args with
  | [.num ⟨.int .i32, tg⟩, .num ⟨.int .i32, pp⟩, .num ⟨.int .i32, cp⟩, .num ⟨.int .i32, n⟩] =>
      (tagOf tg).bind fun t =>
        (o.segment pp.toNat (valsWidth (S.params t))).bind fun bs =>
          (readVals (S.params t) bs).bind fun a =>
            (o.segment cp.toNat (4 * n.toNat)).bind fun cs => (le32s cs).bind fun hs =>
              if (S.arity t).Admits hs.length then some (⟨t, a⟩, hs) else none
  | _ => none

/-- **The write of an answered call**: `node` answered with a handle. -/
def witWrite (ix : WitImports) (o : Callout) (w : HostReply) : Option (WitWEv S) := do
  let r ← replyI32 w
  if o.imp = ix.node then
    let (op, hs) ← Callout.witNode S tagOf o
    return .write op hs r
  else none

/-- A call of `accept(h)`. -/
def witAccept (ix : WitImports) (o : Callout) : Option (WitWEv S) :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the typed AST writer: accepts at calls, writes at answers. -/
def witRoles (ix : WitImports) : Roles Unit (WitWEv S) Unit Unit where
  callIn := witAccept S ix
  answerIn := witWrite S tagOf ix

/-- **The writer traces of a module** through the typed AST imports. -/
def witTraces (P : Numerics.Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : WitImports) : Set (List (WitWEv S)) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (witRoles S tagOf ix)

/-- **The writer language of a module** through the typed AST imports. -/
def witWriterLang (P : Numerics.Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : WitImports) (pol : Policy (BitVec 32)) : Set (AST S.toAstSig) :=
  writerLang (astW S.toAstSig) pol (witTraces S tagOf P Envs memIdx m ix)

/-! ## The example -/

/-- The tags of `calcSig`. -/
inductive CalcTag where
  | num
  | add
  deriving DecidableEq, Repr

/-- **Numbers and sums**: `num` carries an `s64` and no children, `add` exactly two. -/
def calcSig : WitSig where
  Tag := CalcTag
  params
    | .num => [.s64]
    | .add => []
  arity
    | .num => .fixed 0
    | .add => .fixed 2

/-- The tag numbers: `0` is `num`, `1` is `add`. -/
def calcTagOf (tg : BitVec 32) : Option calcSig.Tag :=
  if tg = 0 then some CalcTag.num else if tg = 1 then some CalcTag.add else none

/-- The body of `run`. -/
def calcBody : List Instr :=
  [.intConst .i32 16, .intConst .i64 1, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨0⟩,
   .intConst .i32 16, .intConst .i64 2, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨1⟩,
   .intConst .i32 0, .localGet ⟨0⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 4, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 1, .intConst .i32 0, .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩,
   .call ⟨1⟩]

/-- **The module.** -/
def calcMod : Module where
  types := [Ast.tyTag, tyAcc, tyRun]
  imports := [⟨"wit", "node", .func ⟨0⟩⟩, ⟨"wit", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32, .i32], calcBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The number `num k`. -/
def numTree (k : Int64) : AST calcSig.toAstSig :=
  AST.node (S := calcSig.toAstSig) CalcTag.num (k, ()) []

/-- **The sum `add(num 1, num 2)`.** -/
def addTree : AST calcSig.toAstSig :=
  AST.node (S := calcSig.toAstSig) CalcTag.add () [numTree 1, numTree 2]

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
