module

public import Silmaril.Wasm.Game.HandleAccept.Families.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Probe.Thms
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Tab.Thms
public import Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom.Thms
public import Silmaril.Wasm.Game.HandleAccept.Writer.Builders.Examples
public import Silmaril.Formats.SExp.Api.Thms

/-!
# Atom families × handle APIs: a Wasm module proved sound, with a positive run, for every pair

Every family of `Silmaril.Wasm.Game.HandleAccept.Families` (`Fam`) and every handle API (n-ary
writer, cons writer, n-ary reader, cons reader, AST writer and AST reader at `sexpSig`) has a
core Wasm module whose language is bounded by a Hoare-logic proof (`<family>_<api>_sound`) and
shown non-empty by a concrete traced session (`<family>_<api>_live`). The AST row has two
pairs of theorems, `_astW_` (writer) and `_astR_` (reader). The languages are over the family's
own atom type `Fam.Atom f`: no embedding into another atom type is involved.

## The generic modules

One module per API shape, proved once for every atom type (no per-family proofs):

* **writers** (`Silmaril.Wasm.Game.HandleAccept.MemSound.Tab`): an atom table `T : AtomTable α`
  decodes each atom import `name(ptr, len) -> i32` from the memory bytes at the call. n-ary
  writer: `pairAtomMod name` (calls `name(16, 1)` on `61` and on `62`, stores both handles at
  `[0, 8)`, accepts `sexp(0, 2)`; `tab_pair_lang`: exactly `(a b)`); AST writer at `sexpSig α`:
  the same module, its writes read as `sexpSig` operations (`tab_pairAst_lang`: the branch with
  the leaves `a`, `b`); cons writer: `consAtomMod name` (stores `68 69`, accepts
  `cons(name(0, 2), nil())`; `tab_cons_lang`: exactly `(a)`).
* **readers** (`Silmaril.Wasm.Game.HandleAccept.MemSound.Probe`): `probeMod ix` calls
  `next(h, 0) -> i32` and `leaf(c, retptr)`, then `accept(h)`, for any reader API; the payload
  decoder `pay` reads the atom of `leaf` off the memory after the answer. n-ary reader
  (`naryProbe`: `child`, `atom`; only `firstAtoms`), cons reader (`consProbe`: `get` = car,
  `atom`; only `carAtoms`), AST reader (`astProbe`: `child`, `leaf` = `tag`; only
  `firstLeaves`). Payloads: `bytesPay dec` (a `list<u8>` through the return pointer) and
  `u64Pay` (a `u64` through the return pointer).

## The instantiations

Each family fixes an atom table (writers), the import name of the example, and a byte decoder
(`<family>Dec`, shared by the readers through `bytesPay`); `<family>_list : ListSpec …` records
that the table decodes `61`, `62` to `<family>A`, `<family>B` (the list), and
`<family>_spec : TabSpec …` that it decodes `68 69` to `<family>Hi` (the cons pair and the
readers). Word trees use the existing
`word(ptr)` writer (`Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom`), the instance-play
cons writer `twoWords`, and the `u64` payload for the readers.

| family | writer table (example import) | reader payload | `A`, `B` / `Hi` |
| --- | --- | --- | --- |
| symbols-only | `symbol` (`symbol`) | UTF-8 symbol | `a`, `b` / `hi` |
| byte trees | `blob` (`blob`) | bytes | `61`, `62` / `68 69` |
| word trees | `word(ptr)`, `wordMod`; cons: `twoWords` | `u64` | `42`; cons `(0 1)`; readers `8 + 2 * 2 ^ 32` |
| symbols+strings | `symbol`, `string` (`string`) | UTF-8 string | `"a"`, `"b"` / `"hi"` |
| symbols+bytes | `symbol`, `blob` (`blob`) | bytes | `61`, `62` / `68 69` |
| symbols+strings+bytes | `symbol`, `string`, `blob` (`string`) | UTF-8 string | `"a"`, `"b"` / `"hi"` |
| symbols+strings+keywords | `symbol`, `string`, `keyword` (`keyword`) | UTF-8 keyword | `:a`, `:b` / `:hi` |
| symbols+strings+keywords+bytes | `symbol`, `string`, `keyword`, `blob` (`keyword`) | UTF-8 keyword | `:a`, `:b` / `:hi` |
| Rivest canonical | `blob` (`blob`) | octets | `61`, `62` / `68 69` |
| Rivest hinted | `blob`, hint-free (`blob`) | octets, no hint | `61`, `62` / `68 69` |

For each family `f` (prefix `symbols`, `bytes`, `words`, `symStr`, `symBytes`, `symStrBytes`,
`symStrKw`, `symStrKwBytes`, `rivest`, `hinted`):

| API | theorems | language bound (sound) | accepted (live) |
| --- | --- | --- | --- |
| n-ary writer | `f_naryW_sound`, `f_naryW_live` | `{(A B)}` (words: `{42}`) | `(A B)` (words: `42`) |
| cons writer | `f_consW_sound`, `f_consW_live` | `{(Hi)}` (words: `twoWordsL`) | `(Hi)` (words: `(0 1)`) |
| n-ary reader | `f_naryR_sound`, `f_naryR_live` | `firstAtoms` | `(Hi)` |
| cons reader | `f_consR_sound`, `f_consR_live` | `carAtoms` | `(Hi . nil)` |
| AST writer | `f_astW_sound`, `f_astW_live` | `{SExp.toAST (A B)}` (words: the leaf `42`) | the same |
| AST reader | `f_astR_sound`, `f_astR_live` | `firstLeaves` | `leafNode Hi` |

**Conditions.** Writers: every profile; policies without undefined behaviour (the cons
writers also without sentinel; the word cons writer as in `twoWords_sound`, its live run at the
specification profiles with sentinel `0` or none). Readers: every profile, the trapping read
policy, every accept policy without undefined behaviour, every set of fixed environments
(sound); all fixed environments (live). Admitted hosts: `hiReply`, `consReply`, `probeReply`
(keep the code and the number of memories, may rewrite memory, return the import's result
shape).

**Scope of the examples.** The languages are small: one two-element list, one one-element
cons list, or a reader check of one child. The mixed families' examples use one atom kind each
(the table decodes all of the family's kinds; the reader payload decodes one). Hints of hinted atoms are not read (the
`hinted(hptr, hlen, ptr, len)` writer with hints is `MemSound.Hinted`).

New definitions (the tables, decoders and exemplars); the theorems instantiate `Tab`, `Probe`,
`WordAtom` and `Writers.Builders`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Families

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Cons
  Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms Silmaril.Wasm.Game.HandleAccept.MemSound.Probe
  Silmaril.Wasm.Game.HandleAccept.MemSound.Pair
  Silmaril.Wasm.Game.HandleAccept.MemSound.Tab Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom
open Silmaril.Accept.Handle (Policy OnInvalid writerLang)
open Silmaril.Accept.Handle renaming Env → HEnv

/-! ## Atom decoders -/

theorem utf8_hi : utf8? [0x68, 0x69] = some "hi" := by decide +kernel
theorem utf8_a : utf8? [0x61] = some "a" := by decide +kernel
theorem utf8_b : utf8? [0x62] = some "b" := by decide +kernel

/-- UTF-8 text as a symbol. -/
def symD {ks : List AtomKind} (h : AtomKind.symbol ∈ ks) (bs : List UInt8) : Option (Atom ks) :=
  (utf8? bs).map fun s => ⟨.symbol, h, s⟩

/-- UTF-8 text as a string. -/
def strD {ks : List AtomKind} (h : AtomKind.string ∈ ks) (bs : List UInt8) : Option (Atom ks) :=
  (utf8? bs).map fun s => ⟨.string, h, s⟩

/-- UTF-8 text as a keyword. -/
def kwD {ks : List AtomKind} (h : AtomKind.keyword ∈ ks) (bs : List UInt8) : Option (Atom ks) :=
  (utf8? bs).map fun s => ⟨.keyword, h, s⟩

/-- Bytes as a byte string. -/
def blobD {ks : List AtomKind} (h : AtomKind.bytes ∈ ks) (bs : List UInt8) : Option (Atom ks) :=
  some ⟨.bytes, h, bs⟩

/-! ## The examples' facts -/

/-- **A table entry of an example**: `name` is an example import, `T` decodes its bytes `68 69`
to `a` by `dec`, and names none of `nil`, `cons`, `accept`. -/
structure TabSpec {α : Type} (T : AtomTable α) (name : String) (dec : List UInt8 → Option α)
    (a : α) : Prop where
  hn : name ∈ atomNames
  hT : T.lookup ("sexp", name) = some dec
  hd : dec [0x68, 0x69] = some a
  hnil : T.lookup ("sexp", "nil") = none
  hcons : T.lookup ("sexp", "cons") = none
  hacc : T.lookup ("sexp", "accept") = none

namespace TabSpec

variable {α : Type} {T : AtomTable α} {name : String} {dec : List UInt8 → Option α} {a : α}
  (S : TabSpec T name dec a)
include S

theorem consW_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod name) T {} pol ⊆
      {.cons (.atom a) .nil} :=
  tab_cons_sound P S.hn S.hT S.hd S.hnil S.hcons S.hacc hs hw ha

theorem consW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .cons (.atom a) .nil ∈ tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod name) T {}
      pol :=
  tab_cons_live P S.hn S.hT S.hd S.hnil S.hcons S.hacc pol

end TabSpec

/-- **The facts of a list example**: `name` is an example import, `T` decodes its bytes `61` to
`a` and `62` to `b` by `dec`, and names neither `sexp` nor `accept`. -/
structure ListSpec {α : Type} (T : AtomTable α) (name : String) (dec : List UInt8 → Option α)
    (a b : α) : Prop where
  hn : name ∈ atomNames
  hT : T.lookup ("sexp", name) = some dec
  ha : dec [0x61] = some a
  hb : dec [0x62] = some b
  hsexp : T.lookup ("sexp", "sexp") = none
  hacc : T.lookup ("sexp", "accept") = none

namespace ListSpec

variable {α : Type} {T : AtomTable α} {name : String} {dec : List UInt8 → Option α} {a b : α}
  (S : ListSpec T name dec a b)
include S

theorem naryW_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod name) T {} pol ⊆
      {SExp.ofList [.atom a, .atom b]} :=
  tab_pair_sound P S.hn S.hT S.ha S.hb S.hsexp S.hacc hs hw ha

theorem naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom a, .atom b] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod name) T {} pol :=
  tab_pair_live P S.hn S.hT S.ha S.hb S.hsexp S.hacc pol

theorem astW_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod name) T {} pol =
      {SExp.toAST (SExp.ofList [.atom a, .atom b])} :=
  tab_pairAst_lang P S.hn S.hT S.ha S.hb S.hsexp S.hacc hs hw ha

end ListSpec

/-- The node with the one leaf `x`. -/
abbrev leafNode {α : Type} (x : α) : AST (sexpSig α) :=
  AST.node (S := sexpSig α) SxTag.branch () [AST.node (S := sexpSig α) SxTag.leaf x []]

section Readers

variable {α : Type}

theorem pay_naryR_live (P : Profile) (oa : OnInvalid) (dec : List UInt8 → Option α) {x : α}
    (hd : dec [0x68, 0x69] = some x) :
    SExp.ofList [.atom x] ∈ probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR α (BitVec 32)) (naryProbe (bytesPay dec)) .trap oa Set.univ :=
  nary_live P oa (bytesPay dec) _ fun _ _ hB hw => (bytesPay_page dec 0x68 0x69 hB hw).trans hd

theorem pay_consR_live (P : Profile) (oa : OnInvalid) (dec : List UInt8 → Option α) {x : α}
    (hd : dec [0x68, 0x69] = some x) :
    SExp2.cons (.atom x) .nil ∈ probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR α (BitVec 32)) (consProbe (bytesPay dec)) .trap oa Set.univ :=
  cons_live P oa (bytesPay dec) _ fun _ _ hB hw => (bytesPay_page dec 0x68 0x69 hB hw).trans hd

theorem pay_astR_live (P : Profile) (oa : OnInvalid) (dec : List UInt8 → Option α) {x : α}
    (hd : dec [0x68, 0x69] = some x) :
    leafNode x ∈ probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig α) (BitVec 32)) (astProbe (bytesPay dec)) .trap oa Set.univ :=
  ast_live P oa (bytesPay dec) _ fun _ _ hB hw => (bytesPay_page dec 0x68 0x69 hB hw).trans hd

end Readers

/-! ## The families' tables, decoders and exemplars -/

def symbolsDec : List UInt8 → Option (Fam.Atom .symbols) := utf8?
def symbolsTab : AtomTable (Fam.Atom .symbols) := [(("sexp", "symbol"), symbolsDec)]
def symbolsHi : Fam.Atom .symbols := "hi"
theorem symbols_spec : TabSpec symbolsTab "symbol" symbolsDec symbolsHi :=
  ⟨by decide, rfl, utf8_hi, by simp [symbolsTab], by simp [symbolsTab],
    by simp [symbolsTab]⟩

def bytesDec : List UInt8 → Option (Fam.Atom .bytes) := some
def bytesTab : AtomTable (Fam.Atom .bytes) := [(("sexp", "blob"), bytesDec)]
def bytesHi : Fam.Atom .bytes := [0x68, 0x69]
theorem bytes_spec : TabSpec bytesTab "blob" bytesDec bytesHi :=
  ⟨by decide, rfl, rfl, by simp [bytesTab], by simp [bytesTab], by simp [bytesTab]⟩

def symStrDec : List UInt8 → Option (Fam.Atom .symStr) := strD (by decide)
def symStrTab : AtomTable (Fam.Atom .symStr) :=
  [(("sexp", "symbol"), symD (by decide)), (("sexp", "string"), symStrDec)]
def symStrHi : Fam.Atom .symStr := ⟨.string, by decide, "hi"⟩
theorem symStr_spec : TabSpec symStrTab "string" symStrDec symStrHi :=
  ⟨by decide, rfl, by simp [symStrDec, strD, utf8_hi, symStrHi],
    by simp [symStrTab], by simp [symStrTab], by simp [symStrTab]⟩

def symBytesDec : List UInt8 → Option (Fam.Atom .symBytes) := blobD (by decide)
def symBytesTab : AtomTable (Fam.Atom .symBytes) :=
  [(("sexp", "symbol"), symD (by decide)), (("sexp", "blob"), symBytesDec)]
def symBytesHi : Fam.Atom .symBytes := ⟨.bytes, by decide, [0x68, 0x69]⟩
theorem symBytes_spec : TabSpec symBytesTab "blob" symBytesDec symBytesHi :=
  ⟨by decide, rfl, rfl, by simp [symBytesTab], by simp [symBytesTab],
    by simp [symBytesTab]⟩

def symStrBytesDec : List UInt8 → Option (Fam.Atom .symStrBytes) := strD (by decide)
def symStrBytesTab : AtomTable (Fam.Atom .symStrBytes) :=
  [(("sexp", "symbol"), symD (by decide)), (("sexp", "string"), symStrBytesDec),
    (("sexp", "blob"), blobD (by decide))]
def symStrBytesHi : Fam.Atom .symStrBytes := ⟨.string, by decide, "hi"⟩
theorem symStrBytes_spec : TabSpec symStrBytesTab "string" symStrBytesDec symStrBytesHi :=
  ⟨by decide, rfl, by simp [symStrBytesDec, strD, utf8_hi, symStrBytesHi],
    by simp [symStrBytesTab], by simp [symStrBytesTab], by simp [symStrBytesTab]⟩

def symStrKwDec : List UInt8 → Option (Fam.Atom .symStrKw) := kwD (by decide)
def symStrKwTab : AtomTable (Fam.Atom .symStrKw) :=
  [(("sexp", "symbol"), symD (by decide)), (("sexp", "string"), strD (by decide)),
    (("sexp", "keyword"), symStrKwDec)]
def symStrKwHi : Fam.Atom .symStrKw := ⟨.keyword, by decide, "hi"⟩
theorem symStrKw_spec : TabSpec symStrKwTab "keyword" symStrKwDec symStrKwHi :=
  ⟨by decide, rfl, by simp [symStrKwDec, kwD, utf8_hi, symStrKwHi],
    by simp [symStrKwTab], by simp [symStrKwTab], by simp [symStrKwTab]⟩

def symStrKwBytesDec : List UInt8 → Option (Fam.Atom .symStrKwBytes) := kwD (by decide)
def symStrKwBytesTab : AtomTable (Fam.Atom .symStrKwBytes) :=
  [(("sexp", "symbol"), symD (by decide)), (("sexp", "string"), strD (by decide)),
    (("sexp", "keyword"), symStrKwBytesDec), (("sexp", "blob"), blobD (by decide))]
def symStrKwBytesHi : Fam.Atom .symStrKwBytes := ⟨.keyword, by decide, "hi"⟩
theorem symStrKwBytes_spec :
    TabSpec symStrKwBytesTab "keyword" symStrKwBytesDec symStrKwBytesHi :=
  ⟨by decide, rfl,
    by simp [symStrKwBytesDec, kwD, utf8_hi, symStrKwBytesHi], by simp [symStrKwBytesTab],
    by simp [symStrKwBytesTab], by simp [symStrKwBytesTab]⟩

def rivestDec (bs : List UInt8) : Option (Fam.Atom .rivest) := some (Bytes.ofList bs)
def rivestTab : AtomTable (Fam.Atom .rivest) := [(("sexp", "blob"), rivestDec)]
def rivestHi : Fam.Atom .rivest := Bytes.ofList [0x68, 0x69]
theorem rivest_spec : TabSpec rivestTab "blob" rivestDec rivestHi :=
  ⟨by decide, rfl, rfl, by simp [rivestTab], by simp [rivestTab],
    by simp [rivestTab]⟩

/-- Hint-free hinted atoms. -/
def hintedDec (bs : List UInt8) : Option (Fam.Atom .hinted) := some (none, bs)
def hintedTab : AtomTable (Fam.Atom .hinted) := [(("sexp", "blob"), hintedDec)]
def hintedHi : Fam.Atom .hinted := (none, [0x68, 0x69])
theorem hinted_spec : TabSpec hintedTab "blob" hintedDec hintedHi :=
  ⟨by decide, rfl, rfl, by simp [hintedTab], by simp [hintedTab],
    by simp [hintedTab]⟩


/-! ### The list exemplars -/

def symbolsA : Fam.Atom .symbols := "a"
def symbolsB : Fam.Atom .symbols := "b"
theorem symbols_list :
    ListSpec symbolsTab "symbol" symbolsDec symbolsA symbolsB :=
  ⟨by decide, rfl, utf8_a,
    utf8_b,
    by simp [symbolsTab], by simp [symbolsTab]⟩

def bytesA : Fam.Atom .bytes := [0x61]
def bytesB : Fam.Atom .bytes := [0x62]
theorem bytes_list :
    ListSpec bytesTab "blob" bytesDec bytesA bytesB :=
  ⟨by decide, rfl, rfl,
    rfl,
    by simp [bytesTab], by simp [bytesTab]⟩

def symStrA : Fam.Atom .symStr := ⟨.string, by decide, "a"⟩
def symStrB : Fam.Atom .symStr := ⟨.string, by decide, "b"⟩
theorem symStr_list :
    ListSpec symStrTab "string" symStrDec symStrA symStrB :=
  ⟨by decide, rfl, by simp [symStrDec, strD, utf8_a, symStrA],
    by simp [symStrDec, strD, utf8_b, symStrB],
    by simp [symStrTab], by simp [symStrTab]⟩

def symBytesA : Fam.Atom .symBytes := ⟨.bytes, by decide, [0x61]⟩
def symBytesB : Fam.Atom .symBytes := ⟨.bytes, by decide, [0x62]⟩
theorem symBytes_list :
    ListSpec symBytesTab "blob" symBytesDec symBytesA symBytesB :=
  ⟨by decide, rfl, rfl,
    rfl,
    by simp [symBytesTab], by simp [symBytesTab]⟩

def symStrBytesA : Fam.Atom .symStrBytes := ⟨.string, by decide, "a"⟩
def symStrBytesB : Fam.Atom .symStrBytes := ⟨.string, by decide, "b"⟩
theorem symStrBytes_list :
    ListSpec symStrBytesTab "string" symStrBytesDec symStrBytesA symStrBytesB :=
  ⟨by decide, rfl, by simp [symStrBytesDec, strD, utf8_a, symStrBytesA],
    by simp [symStrBytesDec, strD, utf8_b, symStrBytesB],
    by simp [symStrBytesTab], by simp [symStrBytesTab]⟩

def symStrKwA : Fam.Atom .symStrKw := ⟨.keyword, by decide, "a"⟩
def symStrKwB : Fam.Atom .symStrKw := ⟨.keyword, by decide, "b"⟩
theorem symStrKw_list :
    ListSpec symStrKwTab "keyword" symStrKwDec symStrKwA symStrKwB :=
  ⟨by decide, rfl, by simp [symStrKwDec, kwD, utf8_a, symStrKwA],
    by simp [symStrKwDec, kwD, utf8_b, symStrKwB],
    by simp [symStrKwTab], by simp [symStrKwTab]⟩

def symStrKwBytesA : Fam.Atom .symStrKwBytes := ⟨.keyword, by decide, "a"⟩
def symStrKwBytesB : Fam.Atom .symStrKwBytes := ⟨.keyword, by decide, "b"⟩
theorem symStrKwBytes_list :
    ListSpec symStrKwBytesTab "keyword" symStrKwBytesDec symStrKwBytesA symStrKwBytesB :=
  ⟨by decide, rfl, by simp [symStrKwBytesDec, kwD, utf8_a, symStrKwBytesA],
    by simp [symStrKwBytesDec, kwD, utf8_b, symStrKwBytesB],
    by simp [symStrKwBytesTab], by simp [symStrKwBytesTab]⟩

def rivestA : Fam.Atom .rivest := Bytes.ofList [0x61]
def rivestB : Fam.Atom .rivest := Bytes.ofList [0x62]
theorem rivest_list :
    ListSpec rivestTab "blob" rivestDec rivestA rivestB :=
  ⟨by decide, rfl, rfl,
    rfl,
    by simp [rivestTab], by simp [rivestTab]⟩

def hintedA : Fam.Atom .hinted := (none, [0x61])
def hintedB : Fam.Atom .hinted := (none, [0x62])
theorem hinted_list :
    ListSpec hintedTab "blob" hintedDec hintedA hintedB :=
  ⟨by decide, rfl, rfl,
    rfl,
    by simp [hintedTab], by simp [hintedTab]⟩

/-! ## The pairs -/

/-! ### word trees (`Fam.words`) -/

/-- The AST writer language of a module through `word(ptr)` and `sexp(ptr, len)`, its writes
read as `sexpSig` operations. -/
def wordsMemAstWLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : WordImports) (pol : Policy (BitVec 32)) : Set (AST (sexpSig (BitVec 64))) :=
  writerLang (astW (sexpSig (BitVec 64))) pol (astTraces (wordTraces P Envs memIdx m ix))

/-- **word trees, n-ary writer**: `wordMod` writes only `42`. -/
theorem words_naryW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    wordWriterLang P (ReplyEnvs hiReply) 0 wordMod {} pol ⊆ {.atom 42} :=
  word_sound P ha hw

theorem words_naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom 42 ∈ wordWriterLang P (ReplyEnvs hiReply) 0 wordMod {} pol :=
  word_live P pol

/-- **word trees, cons writer**: `twoWords` writes only lists `(x x+1)`. -/
theorem words_consW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    wordsConsWLang P Writers.Builders.twoWords Writers.Builders.twoIx pol ⊆
      Writers.Builders.twoWordsL :=
  Writers.Builders.twoWords_sound P hs hw ha

theorem words_consW_live (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : ∀ r, pol.sentinel = some r → r = 0) :
    SExp2.ofAtoms [0, 1] ∈
      wordsConsWLang (Profile.spec nd {}) Writers.Builders.twoWords Writers.Builders.twoIx pol :=
  Writers.Builders.twoWords_accepts_0_spec nd hs

theorem words_astW_lang (P : Profile) {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    wordsMemAstWLang P (ReplyEnvs hiReply) 0 wordMod {} pol = {SExp.toAST (.atom 42)} := by
  rw [wordsMemAstWLang, astTraces, sexpLang_eq_astLang ha hw]
  exact (congrArg (SExp.toAST '' ·) (word_lang P ha hw)).trans Set.image_singleton

/-- **word trees, AST writer**: `wordMod` writes only the leaf `42`. -/
theorem words_astW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    wordsMemAstWLang P (ReplyEnvs hiReply) 0 wordMod {} pol ⊆ {SExp.toAST (.atom 42)} :=
  (words_astW_lang P ha hw).subset

theorem words_astW_live (P : Profile) {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    SExp.toAST (.atom 42) ∈ wordsMemAstWLang P (ReplyEnvs hiReply) 0 wordMod {} pol := by
  rw [words_astW_lang P ha hw]; rfl

/-- **word trees, n-ary reader**: only lists whose first child is an atom. -/
theorem words_naryR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp (Fam.Atom .words)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR (Fam.Atom .words) (BitVec 32)) (naryProbe u64Pay) .trap oa Rhos ⊆
      firstAtoms (Fam.Atom .words) :=
  nary_sound P _ hoa Rhos

theorem words_naryR_live (P : Profile) (oa : OnInvalid) :
    SExp.ofList [.atom (8 + 2 * 2 ^ 32)] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
        (sexpR (Fam.Atom .words) (BitVec 32)) (naryProbe u64Pay) .trap oa Set.univ :=
  nary_live P oa u64Pay 0 fun _ _ hB hw => u64Pay_page 0 hB hw

/-- **word trees, cons reader**: only pairs whose car is an atom. -/
theorem words_consR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp2 (Fam.Atom .words)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR (Fam.Atom .words) (BitVec 32)) (consProbe u64Pay) .trap oa Rhos ⊆
      carAtoms (Fam.Atom .words) :=
  cons_sound P _ hoa Rhos

theorem words_consR_live (P : Profile) (oa : OnInvalid) :
    SExp2.cons (.atom (8 + 2 * 2 ^ 32)) .nil ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
        (consR (Fam.Atom .words) (BitVec 32)) (consProbe u64Pay) .trap oa Set.univ :=
  cons_live P oa u64Pay 0 fun _ _ hB hw => u64Pay_page 0 hB hw

/-- **word trees, AST reader**: only nodes whose first child is a leaf. -/
theorem words_astR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (AST (sexpSig (Fam.Atom .words))))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig (Fam.Atom .words)) (BitVec 32)) (astProbe u64Pay) .trap oa Rhos ⊆
      firstLeaves (Fam.Atom .words) :=
  ast_sound P _ hoa Rhos

theorem words_astR_live (P : Profile) (oa : OnInvalid) :
    leafNode (8 + 2 * 2 ^ 32 : Fam.Atom .words) ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
        (astR (sexpSig (Fam.Atom .words)) (BitVec 32)) (astProbe u64Pay) .trap oa Set.univ :=
  ast_live P oa u64Pay 0 fun _ _ hB hw => u64Pay_page 0 hB hw

/-! ### symbols-only (`Fam.symbols`) -/

/-- **symbols-only, n-ary writer**:
`pairAtomMod "symbol"` writes only `(symbolsA symbolsB)`. -/
theorem symbols_naryW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "symbol") symbolsTab {} pol ⊆
      {SExp.ofList [.atom symbolsA, .atom symbolsB]} :=
  symbols_list.naryW_sound P hs hw ha

theorem symbols_naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom symbolsA, .atom symbolsB] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "symbol") symbolsTab {} pol :=
  symbols_list.naryW_live P pol

/-- **symbols-only, cons writer**:
`consAtomMod "symbol"` writes only `(symbolsHi)`. -/
theorem symbols_consW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "symbol") symbolsTab {} pol ⊆
      {.cons (.atom symbolsHi) .nil} :=
  symbols_spec.consW_sound P hs hw ha

theorem symbols_consW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .cons (.atom symbolsHi) .nil ∈
      tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "symbol") symbolsTab {} pol :=
  symbols_spec.consW_live P pol

/-- **symbols-only, AST writer**:
`pairAtomMod "symbol"` writes only the branch with leaves `symbolsA`, `symbolsB`. -/
theorem symbols_astW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "symbol") symbolsTab {} pol ⊆
      {SExp.toAST (SExp.ofList [.atom symbolsA, .atom symbolsB])} :=
  (symbols_list.astW_lang P hs hw ha).subset

theorem symbols_astW_live (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    SExp.toAST (SExp.ofList [.atom symbolsA, .atom symbolsB]) ∈
      tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "symbol") symbolsTab {}
        pol := by
  rw [symbols_list.astW_lang P hs hw ha]; rfl

/-- **symbols-only, n-ary reader**:
only lists whose first child is an atom. -/
theorem symbols_naryR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp (Fam.Atom .symbols)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR (Fam.Atom .symbols) (BitVec 32))
      (naryProbe (bytesPay symbolsDec)) .trap oa Rhos ⊆
      firstAtoms (Fam.Atom .symbols) :=
  nary_sound P _ hoa Rhos

theorem symbols_naryR_live (P : Profile) (oa : OnInvalid) :
    SExp.ofList [.atom symbolsHi] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
        (sexpR (Fam.Atom .symbols) (BitVec 32))
        (naryProbe (bytesPay symbolsDec)) .trap oa Set.univ :=
  pay_naryR_live P oa symbolsDec symbols_spec.hd

/-- **symbols-only, cons reader**:
only pairs whose car is an atom. -/
theorem symbols_consR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp2 (Fam.Atom .symbols)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR (Fam.Atom .symbols) (BitVec 32))
      (consProbe (bytesPay symbolsDec)) .trap oa Rhos ⊆
      carAtoms (Fam.Atom .symbols) :=
  cons_sound P _ hoa Rhos

theorem symbols_consR_live (P : Profile) (oa : OnInvalid) :
    SExp2.cons (.atom symbolsHi) .nil ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
        (consR (Fam.Atom .symbols) (BitVec 32))
        (consProbe (bytesPay symbolsDec)) .trap oa Set.univ :=
  pay_consR_live P oa symbolsDec symbols_spec.hd

/-- **symbols-only, AST reader**:
only nodes whose first child is a leaf. -/
theorem symbols_astR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (AST (sexpSig (Fam.Atom .symbols))))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig (Fam.Atom .symbols)) (BitVec 32))
      (astProbe (bytesPay symbolsDec)) .trap oa Rhos ⊆
      firstLeaves (Fam.Atom .symbols) :=
  ast_sound P _ hoa Rhos

theorem symbols_astR_live (P : Profile) (oa : OnInvalid) :
    leafNode symbolsHi ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
        (astR (sexpSig (Fam.Atom .symbols)) (BitVec 32))
        (astProbe (bytesPay symbolsDec)) .trap oa Set.univ :=
  pay_astR_live P oa symbolsDec symbols_spec.hd

/-! ### byte trees (`Fam.bytes`) -/

/-- **byte trees, n-ary writer**:
`pairAtomMod "blob"` writes only `(bytesA bytesB)`. -/
theorem bytes_naryW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") bytesTab {} pol ⊆
      {SExp.ofList [.atom bytesA, .atom bytesB]} :=
  bytes_list.naryW_sound P hs hw ha

theorem bytes_naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom bytesA, .atom bytesB] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") bytesTab {} pol :=
  bytes_list.naryW_live P pol

/-- **byte trees, cons writer**:
`consAtomMod "blob"` writes only `(bytesHi)`. -/
theorem bytes_consW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "blob") bytesTab {} pol ⊆
      {.cons (.atom bytesHi) .nil} :=
  bytes_spec.consW_sound P hs hw ha

theorem bytes_consW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .cons (.atom bytesHi) .nil ∈
      tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "blob") bytesTab {} pol :=
  bytes_spec.consW_live P pol

/-- **byte trees, AST writer**:
`pairAtomMod "blob"` writes only the branch with leaves `bytesA`, `bytesB`. -/
theorem bytes_astW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") bytesTab {} pol ⊆
      {SExp.toAST (SExp.ofList [.atom bytesA, .atom bytesB])} :=
  (bytes_list.astW_lang P hs hw ha).subset

theorem bytes_astW_live (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    SExp.toAST (SExp.ofList [.atom bytesA, .atom bytesB]) ∈
      tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") bytesTab {}
        pol := by
  rw [bytes_list.astW_lang P hs hw ha]; rfl

/-- **byte trees, n-ary reader**:
only lists whose first child is an atom. -/
theorem bytes_naryR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp (Fam.Atom .bytes)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR (Fam.Atom .bytes) (BitVec 32))
      (naryProbe (bytesPay bytesDec)) .trap oa Rhos ⊆
      firstAtoms (Fam.Atom .bytes) :=
  nary_sound P _ hoa Rhos

theorem bytes_naryR_live (P : Profile) (oa : OnInvalid) :
    SExp.ofList [.atom bytesHi] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
        (sexpR (Fam.Atom .bytes) (BitVec 32))
        (naryProbe (bytesPay bytesDec)) .trap oa Set.univ :=
  pay_naryR_live P oa bytesDec bytes_spec.hd

/-- **byte trees, cons reader**:
only pairs whose car is an atom. -/
theorem bytes_consR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp2 (Fam.Atom .bytes)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR (Fam.Atom .bytes) (BitVec 32))
      (consProbe (bytesPay bytesDec)) .trap oa Rhos ⊆
      carAtoms (Fam.Atom .bytes) :=
  cons_sound P _ hoa Rhos

theorem bytes_consR_live (P : Profile) (oa : OnInvalid) :
    SExp2.cons (.atom bytesHi) .nil ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
        (consR (Fam.Atom .bytes) (BitVec 32))
        (consProbe (bytesPay bytesDec)) .trap oa Set.univ :=
  pay_consR_live P oa bytesDec bytes_spec.hd

/-- **byte trees, AST reader**:
only nodes whose first child is a leaf. -/
theorem bytes_astR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (AST (sexpSig (Fam.Atom .bytes))))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig (Fam.Atom .bytes)) (BitVec 32))
      (astProbe (bytesPay bytesDec)) .trap oa Rhos ⊆
      firstLeaves (Fam.Atom .bytes) :=
  ast_sound P _ hoa Rhos

theorem bytes_astR_live (P : Profile) (oa : OnInvalid) :
    leafNode bytesHi ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
        (astR (sexpSig (Fam.Atom .bytes)) (BitVec 32))
        (astProbe (bytesPay bytesDec)) .trap oa Set.univ :=
  pay_astR_live P oa bytesDec bytes_spec.hd

/-! ### symbols+strings (`Fam.symStr`) -/

/-- **symbols+strings, n-ary writer**:
`pairAtomMod "string"` writes only `(symStrA symStrB)`. -/
theorem symStr_naryW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "string") symStrTab {} pol ⊆
      {SExp.ofList [.atom symStrA, .atom symStrB]} :=
  symStr_list.naryW_sound P hs hw ha

theorem symStr_naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom symStrA, .atom symStrB] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "string") symStrTab {} pol :=
  symStr_list.naryW_live P pol

/-- **symbols+strings, cons writer**:
`consAtomMod "string"` writes only `(symStrHi)`. -/
theorem symStr_consW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "string") symStrTab {} pol ⊆
      {.cons (.atom symStrHi) .nil} :=
  symStr_spec.consW_sound P hs hw ha

theorem symStr_consW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .cons (.atom symStrHi) .nil ∈
      tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "string") symStrTab {} pol :=
  symStr_spec.consW_live P pol

/-- **symbols+strings, AST writer**:
`pairAtomMod "string"` writes only the branch with leaves `symStrA`, `symStrB`. -/
theorem symStr_astW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "string") symStrTab {} pol ⊆
      {SExp.toAST (SExp.ofList [.atom symStrA, .atom symStrB])} :=
  (symStr_list.astW_lang P hs hw ha).subset

theorem symStr_astW_live (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    SExp.toAST (SExp.ofList [.atom symStrA, .atom symStrB]) ∈
      tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "string") symStrTab {}
        pol := by
  rw [symStr_list.astW_lang P hs hw ha]; rfl

/-- **symbols+strings, n-ary reader**:
only lists whose first child is an atom. -/
theorem symStr_naryR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp (Fam.Atom .symStr)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR (Fam.Atom .symStr) (BitVec 32))
      (naryProbe (bytesPay symStrDec)) .trap oa Rhos ⊆
      firstAtoms (Fam.Atom .symStr) :=
  nary_sound P _ hoa Rhos

theorem symStr_naryR_live (P : Profile) (oa : OnInvalid) :
    SExp.ofList [.atom symStrHi] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
        (sexpR (Fam.Atom .symStr) (BitVec 32))
        (naryProbe (bytesPay symStrDec)) .trap oa Set.univ :=
  pay_naryR_live P oa symStrDec symStr_spec.hd

/-- **symbols+strings, cons reader**:
only pairs whose car is an atom. -/
theorem symStr_consR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp2 (Fam.Atom .symStr)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR (Fam.Atom .symStr) (BitVec 32))
      (consProbe (bytesPay symStrDec)) .trap oa Rhos ⊆
      carAtoms (Fam.Atom .symStr) :=
  cons_sound P _ hoa Rhos

theorem symStr_consR_live (P : Profile) (oa : OnInvalid) :
    SExp2.cons (.atom symStrHi) .nil ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
        (consR (Fam.Atom .symStr) (BitVec 32))
        (consProbe (bytesPay symStrDec)) .trap oa Set.univ :=
  pay_consR_live P oa symStrDec symStr_spec.hd

/-- **symbols+strings, AST reader**:
only nodes whose first child is a leaf. -/
theorem symStr_astR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (AST (sexpSig (Fam.Atom .symStr))))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig (Fam.Atom .symStr)) (BitVec 32))
      (astProbe (bytesPay symStrDec)) .trap oa Rhos ⊆
      firstLeaves (Fam.Atom .symStr) :=
  ast_sound P _ hoa Rhos

theorem symStr_astR_live (P : Profile) (oa : OnInvalid) :
    leafNode symStrHi ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
        (astR (sexpSig (Fam.Atom .symStr)) (BitVec 32))
        (astProbe (bytesPay symStrDec)) .trap oa Set.univ :=
  pay_astR_live P oa symStrDec symStr_spec.hd

/-! ### symbols+bytes (`Fam.symBytes`) -/

/-- **symbols+bytes, n-ary writer**:
`pairAtomMod "blob"` writes only `(symBytesA symBytesB)`. -/
theorem symBytes_naryW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") symBytesTab {} pol ⊆
      {SExp.ofList [.atom symBytesA, .atom symBytesB]} :=
  symBytes_list.naryW_sound P hs hw ha

theorem symBytes_naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom symBytesA, .atom symBytesB] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") symBytesTab {} pol :=
  symBytes_list.naryW_live P pol

/-- **symbols+bytes, cons writer**:
`consAtomMod "blob"` writes only `(symBytesHi)`. -/
theorem symBytes_consW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "blob") symBytesTab {} pol ⊆
      {.cons (.atom symBytesHi) .nil} :=
  symBytes_spec.consW_sound P hs hw ha

theorem symBytes_consW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .cons (.atom symBytesHi) .nil ∈
      tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "blob") symBytesTab {} pol :=
  symBytes_spec.consW_live P pol

/-- **symbols+bytes, AST writer**:
`pairAtomMod "blob"` writes only the branch with leaves `symBytesA`, `symBytesB`. -/
theorem symBytes_astW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") symBytesTab {} pol ⊆
      {SExp.toAST (SExp.ofList [.atom symBytesA, .atom symBytesB])} :=
  (symBytes_list.astW_lang P hs hw ha).subset

theorem symBytes_astW_live (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    SExp.toAST (SExp.ofList [.atom symBytesA, .atom symBytesB]) ∈
      tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") symBytesTab {}
        pol := by
  rw [symBytes_list.astW_lang P hs hw ha]; rfl

/-- **symbols+bytes, n-ary reader**:
only lists whose first child is an atom. -/
theorem symBytes_naryR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp (Fam.Atom .symBytes)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR (Fam.Atom .symBytes) (BitVec 32))
      (naryProbe (bytesPay symBytesDec)) .trap oa Rhos ⊆
      firstAtoms (Fam.Atom .symBytes) :=
  nary_sound P _ hoa Rhos

theorem symBytes_naryR_live (P : Profile) (oa : OnInvalid) :
    SExp.ofList [.atom symBytesHi] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
        (sexpR (Fam.Atom .symBytes) (BitVec 32))
        (naryProbe (bytesPay symBytesDec)) .trap oa Set.univ :=
  pay_naryR_live P oa symBytesDec symBytes_spec.hd

/-- **symbols+bytes, cons reader**:
only pairs whose car is an atom. -/
theorem symBytes_consR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp2 (Fam.Atom .symBytes)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR (Fam.Atom .symBytes) (BitVec 32))
      (consProbe (bytesPay symBytesDec)) .trap oa Rhos ⊆
      carAtoms (Fam.Atom .symBytes) :=
  cons_sound P _ hoa Rhos

theorem symBytes_consR_live (P : Profile) (oa : OnInvalid) :
    SExp2.cons (.atom symBytesHi) .nil ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
        (consR (Fam.Atom .symBytes) (BitVec 32))
        (consProbe (bytesPay symBytesDec)) .trap oa Set.univ :=
  pay_consR_live P oa symBytesDec symBytes_spec.hd

/-- **symbols+bytes, AST reader**:
only nodes whose first child is a leaf. -/
theorem symBytes_astR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (AST (sexpSig (Fam.Atom .symBytes))))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig (Fam.Atom .symBytes)) (BitVec 32))
      (astProbe (bytesPay symBytesDec)) .trap oa Rhos ⊆
      firstLeaves (Fam.Atom .symBytes) :=
  ast_sound P _ hoa Rhos

theorem symBytes_astR_live (P : Profile) (oa : OnInvalid) :
    leafNode symBytesHi ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
        (astR (sexpSig (Fam.Atom .symBytes)) (BitVec 32))
        (astProbe (bytesPay symBytesDec)) .trap oa Set.univ :=
  pay_astR_live P oa symBytesDec symBytes_spec.hd

/-! ### symbols+strings+bytes (`Fam.symStrBytes`) -/

/-- **symbols+strings+bytes, n-ary writer**:
`pairAtomMod "string"` writes only `(symStrBytesA symStrBytesB)`. -/
theorem symStrBytes_naryW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "string") symStrBytesTab {} pol ⊆
      {SExp.ofList [.atom symStrBytesA, .atom symStrBytesB]} :=
  symStrBytes_list.naryW_sound P hs hw ha

theorem symStrBytes_naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom symStrBytesA, .atom symStrBytesB] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "string") symStrBytesTab {} pol :=
  symStrBytes_list.naryW_live P pol

/-- **symbols+strings+bytes, cons writer**:
`consAtomMod "string"` writes only `(symStrBytesHi)`. -/
theorem symStrBytes_consW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "string") symStrBytesTab {} pol ⊆
      {.cons (.atom symStrBytesHi) .nil} :=
  symStrBytes_spec.consW_sound P hs hw ha

theorem symStrBytes_consW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .cons (.atom symStrBytesHi) .nil ∈
      tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "string") symStrBytesTab {} pol :=
  symStrBytes_spec.consW_live P pol

/-- **symbols+strings+bytes, AST writer**:
`pairAtomMod "string"` writes only the branch with leaves `symStrBytesA`, `symStrBytesB`. -/
theorem symStrBytes_astW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "string") symStrBytesTab {} pol ⊆
      {SExp.toAST (SExp.ofList [.atom symStrBytesA, .atom symStrBytesB])} :=
  (symStrBytes_list.astW_lang P hs hw ha).subset

theorem symStrBytes_astW_live (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    SExp.toAST (SExp.ofList [.atom symStrBytesA, .atom symStrBytesB]) ∈
      tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "string") symStrBytesTab {}
        pol := by
  rw [symStrBytes_list.astW_lang P hs hw ha]; rfl

/-- **symbols+strings+bytes, n-ary reader**:
only lists whose first child is an atom. -/
theorem symStrBytes_naryR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp (Fam.Atom .symStrBytes)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR (Fam.Atom .symStrBytes) (BitVec 32))
      (naryProbe (bytesPay symStrBytesDec)) .trap oa Rhos ⊆
      firstAtoms (Fam.Atom .symStrBytes) :=
  nary_sound P _ hoa Rhos

theorem symStrBytes_naryR_live (P : Profile) (oa : OnInvalid) :
    SExp.ofList [.atom symStrBytesHi] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
        (sexpR (Fam.Atom .symStrBytes) (BitVec 32))
        (naryProbe (bytesPay symStrBytesDec)) .trap oa Set.univ :=
  pay_naryR_live P oa symStrBytesDec symStrBytes_spec.hd

/-- **symbols+strings+bytes, cons reader**:
only pairs whose car is an atom. -/
theorem symStrBytes_consR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp2 (Fam.Atom .symStrBytes)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR (Fam.Atom .symStrBytes) (BitVec 32))
      (consProbe (bytesPay symStrBytesDec)) .trap oa Rhos ⊆
      carAtoms (Fam.Atom .symStrBytes) :=
  cons_sound P _ hoa Rhos

theorem symStrBytes_consR_live (P : Profile) (oa : OnInvalid) :
    SExp2.cons (.atom symStrBytesHi) .nil ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
        (consR (Fam.Atom .symStrBytes) (BitVec 32))
        (consProbe (bytesPay symStrBytesDec)) .trap oa Set.univ :=
  pay_consR_live P oa symStrBytesDec symStrBytes_spec.hd

/-- **symbols+strings+bytes, AST reader**:
only nodes whose first child is a leaf. -/
theorem symStrBytes_astR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (AST (sexpSig (Fam.Atom .symStrBytes))))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig (Fam.Atom .symStrBytes)) (BitVec 32))
      (astProbe (bytesPay symStrBytesDec)) .trap oa Rhos ⊆
      firstLeaves (Fam.Atom .symStrBytes) :=
  ast_sound P _ hoa Rhos

theorem symStrBytes_astR_live (P : Profile) (oa : OnInvalid) :
    leafNode symStrBytesHi ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
        (astR (sexpSig (Fam.Atom .symStrBytes)) (BitVec 32))
        (astProbe (bytesPay symStrBytesDec)) .trap oa Set.univ :=
  pay_astR_live P oa symStrBytesDec symStrBytes_spec.hd

/-! ### symbols+strings+keywords (`Fam.symStrKw`) -/

/-- **symbols+strings+keywords, n-ary writer**:
`pairAtomMod "keyword"` writes only `(symStrKwA symStrKwB)`. -/
theorem symStrKw_naryW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "keyword") symStrKwTab {} pol ⊆
      {SExp.ofList [.atom symStrKwA, .atom symStrKwB]} :=
  symStrKw_list.naryW_sound P hs hw ha

theorem symStrKw_naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom symStrKwA, .atom symStrKwB] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "keyword") symStrKwTab {} pol :=
  symStrKw_list.naryW_live P pol

/-- **symbols+strings+keywords, cons writer**:
`consAtomMod "keyword"` writes only `(symStrKwHi)`. -/
theorem symStrKw_consW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "keyword") symStrKwTab {} pol ⊆
      {.cons (.atom symStrKwHi) .nil} :=
  symStrKw_spec.consW_sound P hs hw ha

theorem symStrKw_consW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .cons (.atom symStrKwHi) .nil ∈
      tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "keyword") symStrKwTab {} pol :=
  symStrKw_spec.consW_live P pol

/-- **symbols+strings+keywords, AST writer**:
`pairAtomMod "keyword"` writes only the branch with leaves `symStrKwA`, `symStrKwB`. -/
theorem symStrKw_astW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "keyword") symStrKwTab {} pol ⊆
      {SExp.toAST (SExp.ofList [.atom symStrKwA, .atom symStrKwB])} :=
  (symStrKw_list.astW_lang P hs hw ha).subset

theorem symStrKw_astW_live (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    SExp.toAST (SExp.ofList [.atom symStrKwA, .atom symStrKwB]) ∈
      tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "keyword") symStrKwTab {}
        pol := by
  rw [symStrKw_list.astW_lang P hs hw ha]; rfl

/-- **symbols+strings+keywords, n-ary reader**:
only lists whose first child is an atom. -/
theorem symStrKw_naryR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp (Fam.Atom .symStrKw)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR (Fam.Atom .symStrKw) (BitVec 32))
      (naryProbe (bytesPay symStrKwDec)) .trap oa Rhos ⊆
      firstAtoms (Fam.Atom .symStrKw) :=
  nary_sound P _ hoa Rhos

theorem symStrKw_naryR_live (P : Profile) (oa : OnInvalid) :
    SExp.ofList [.atom symStrKwHi] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
        (sexpR (Fam.Atom .symStrKw) (BitVec 32))
        (naryProbe (bytesPay symStrKwDec)) .trap oa Set.univ :=
  pay_naryR_live P oa symStrKwDec symStrKw_spec.hd

/-- **symbols+strings+keywords, cons reader**:
only pairs whose car is an atom. -/
theorem symStrKw_consR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp2 (Fam.Atom .symStrKw)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR (Fam.Atom .symStrKw) (BitVec 32))
      (consProbe (bytesPay symStrKwDec)) .trap oa Rhos ⊆
      carAtoms (Fam.Atom .symStrKw) :=
  cons_sound P _ hoa Rhos

theorem symStrKw_consR_live (P : Profile) (oa : OnInvalid) :
    SExp2.cons (.atom symStrKwHi) .nil ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
        (consR (Fam.Atom .symStrKw) (BitVec 32))
        (consProbe (bytesPay symStrKwDec)) .trap oa Set.univ :=
  pay_consR_live P oa symStrKwDec symStrKw_spec.hd

/-- **symbols+strings+keywords, AST reader**:
only nodes whose first child is a leaf. -/
theorem symStrKw_astR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (AST (sexpSig (Fam.Atom .symStrKw))))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig (Fam.Atom .symStrKw)) (BitVec 32))
      (astProbe (bytesPay symStrKwDec)) .trap oa Rhos ⊆
      firstLeaves (Fam.Atom .symStrKw) :=
  ast_sound P _ hoa Rhos

theorem symStrKw_astR_live (P : Profile) (oa : OnInvalid) :
    leafNode symStrKwHi ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
        (astR (sexpSig (Fam.Atom .symStrKw)) (BitVec 32))
        (astProbe (bytesPay symStrKwDec)) .trap oa Set.univ :=
  pay_astR_live P oa symStrKwDec symStrKw_spec.hd

/-! ### symbols+strings+keywords+bytes (`Fam.symStrKwBytes`) -/

/-- **symbols+strings+keywords+bytes, n-ary writer**:
`pairAtomMod "keyword"` writes only `(symStrKwBytesA symStrKwBytesB)`. -/
theorem symStrKwBytes_naryW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "keyword") symStrKwBytesTab {} pol ⊆
      {SExp.ofList [.atom symStrKwBytesA, .atom symStrKwBytesB]} :=
  symStrKwBytes_list.naryW_sound P hs hw ha

theorem symStrKwBytes_naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom symStrKwBytesA, .atom symStrKwBytesB] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "keyword") symStrKwBytesTab {} pol :=
  symStrKwBytes_list.naryW_live P pol

/-- **symbols+strings+keywords+bytes, cons writer**:
`consAtomMod "keyword"` writes only `(symStrKwBytesHi)`. -/
theorem symStrKwBytes_consW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "keyword") symStrKwBytesTab {} pol ⊆
      {.cons (.atom symStrKwBytesHi) .nil} :=
  symStrKwBytes_spec.consW_sound P hs hw ha

theorem symStrKwBytes_consW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .cons (.atom symStrKwBytesHi) .nil ∈
      tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "keyword") symStrKwBytesTab {} pol :=
  symStrKwBytes_spec.consW_live P pol

/-- **symbols+strings+keywords+bytes, AST writer**:
`pairAtomMod "keyword"` writes only the branch with leaves `symStrKwBytesA`, `symStrKwBytesB`. -/
theorem symStrKwBytes_astW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "keyword") symStrKwBytesTab {} pol ⊆
      {SExp.toAST (SExp.ofList [.atom symStrKwBytesA, .atom symStrKwBytesB])} :=
  (symStrKwBytes_list.astW_lang P hs hw ha).subset

theorem symStrKwBytes_astW_live (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    SExp.toAST (SExp.ofList [.atom symStrKwBytesA, .atom symStrKwBytesB]) ∈
      tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "keyword") symStrKwBytesTab {}
        pol := by
  rw [symStrKwBytes_list.astW_lang P hs hw ha]; rfl

/-- **symbols+strings+keywords+bytes, n-ary reader**:
only lists whose first child is an atom. -/
theorem symStrKwBytes_naryR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp (Fam.Atom .symStrKwBytes)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR (Fam.Atom .symStrKwBytes) (BitVec 32))
      (naryProbe (bytesPay symStrKwBytesDec)) .trap oa Rhos ⊆
      firstAtoms (Fam.Atom .symStrKwBytes) :=
  nary_sound P _ hoa Rhos

theorem symStrKwBytes_naryR_live (P : Profile) (oa : OnInvalid) :
    SExp.ofList [.atom symStrKwBytesHi] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
        (sexpR (Fam.Atom .symStrKwBytes) (BitVec 32))
        (naryProbe (bytesPay symStrKwBytesDec)) .trap oa Set.univ :=
  pay_naryR_live P oa symStrKwBytesDec symStrKwBytes_spec.hd

/-- **symbols+strings+keywords+bytes, cons reader**:
only pairs whose car is an atom. -/
theorem symStrKwBytes_consR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp2 (Fam.Atom .symStrKwBytes)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR (Fam.Atom .symStrKwBytes) (BitVec 32))
      (consProbe (bytesPay symStrKwBytesDec)) .trap oa Rhos ⊆
      carAtoms (Fam.Atom .symStrKwBytes) :=
  cons_sound P _ hoa Rhos

theorem symStrKwBytes_consR_live (P : Profile) (oa : OnInvalid) :
    SExp2.cons (.atom symStrKwBytesHi) .nil ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
        (consR (Fam.Atom .symStrKwBytes) (BitVec 32))
        (consProbe (bytesPay symStrKwBytesDec)) .trap oa Set.univ :=
  pay_consR_live P oa symStrKwBytesDec symStrKwBytes_spec.hd

/-- **symbols+strings+keywords+bytes, AST reader**:
only nodes whose first child is a leaf. -/
theorem symStrKwBytes_astR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (AST (sexpSig (Fam.Atom .symStrKwBytes))))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig (Fam.Atom .symStrKwBytes)) (BitVec 32))
      (astProbe (bytesPay symStrKwBytesDec)) .trap oa Rhos ⊆
      firstLeaves (Fam.Atom .symStrKwBytes) :=
  ast_sound P _ hoa Rhos

theorem symStrKwBytes_astR_live (P : Profile) (oa : OnInvalid) :
    leafNode symStrKwBytesHi ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
        (astR (sexpSig (Fam.Atom .symStrKwBytes)) (BitVec 32))
        (astProbe (bytesPay symStrKwBytesDec)) .trap oa Set.univ :=
  pay_astR_live P oa symStrKwBytesDec symStrKwBytes_spec.hd

/-! ### Rivest canonical (`Fam.rivest`) -/

/-- **Rivest canonical, n-ary writer**:
`pairAtomMod "blob"` writes only `(rivestA rivestB)`. -/
theorem rivest_naryW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") rivestTab {} pol ⊆
      {SExp.ofList [.atom rivestA, .atom rivestB]} :=
  rivest_list.naryW_sound P hs hw ha

theorem rivest_naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom rivestA, .atom rivestB] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") rivestTab {} pol :=
  rivest_list.naryW_live P pol

/-- **Rivest canonical, cons writer**:
`consAtomMod "blob"` writes only `(rivestHi)`. -/
theorem rivest_consW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "blob") rivestTab {} pol ⊆
      {.cons (.atom rivestHi) .nil} :=
  rivest_spec.consW_sound P hs hw ha

theorem rivest_consW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .cons (.atom rivestHi) .nil ∈
      tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "blob") rivestTab {} pol :=
  rivest_spec.consW_live P pol

/-- **Rivest canonical, AST writer**:
`pairAtomMod "blob"` writes only the branch with leaves `rivestA`, `rivestB`. -/
theorem rivest_astW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") rivestTab {} pol ⊆
      {SExp.toAST (SExp.ofList [.atom rivestA, .atom rivestB])} :=
  (rivest_list.astW_lang P hs hw ha).subset

theorem rivest_astW_live (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    SExp.toAST (SExp.ofList [.atom rivestA, .atom rivestB]) ∈
      tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") rivestTab {}
        pol := by
  rw [rivest_list.astW_lang P hs hw ha]; rfl

/-- **Rivest canonical, n-ary reader**:
only lists whose first child is an atom. -/
theorem rivest_naryR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp (Fam.Atom .rivest)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR (Fam.Atom .rivest) (BitVec 32))
      (naryProbe (bytesPay rivestDec)) .trap oa Rhos ⊆
      firstAtoms (Fam.Atom .rivest) :=
  nary_sound P _ hoa Rhos

theorem rivest_naryR_live (P : Profile) (oa : OnInvalid) :
    SExp.ofList [.atom rivestHi] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
        (sexpR (Fam.Atom .rivest) (BitVec 32))
        (naryProbe (bytesPay rivestDec)) .trap oa Set.univ :=
  pay_naryR_live P oa rivestDec rivest_spec.hd

/-- **Rivest canonical, cons reader**:
only pairs whose car is an atom. -/
theorem rivest_consR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp2 (Fam.Atom .rivest)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR (Fam.Atom .rivest) (BitVec 32))
      (consProbe (bytesPay rivestDec)) .trap oa Rhos ⊆
      carAtoms (Fam.Atom .rivest) :=
  cons_sound P _ hoa Rhos

theorem rivest_consR_live (P : Profile) (oa : OnInvalid) :
    SExp2.cons (.atom rivestHi) .nil ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
        (consR (Fam.Atom .rivest) (BitVec 32))
        (consProbe (bytesPay rivestDec)) .trap oa Set.univ :=
  pay_consR_live P oa rivestDec rivest_spec.hd

/-- **Rivest canonical, AST reader**:
only nodes whose first child is a leaf. -/
theorem rivest_astR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (AST (sexpSig (Fam.Atom .rivest))))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig (Fam.Atom .rivest)) (BitVec 32))
      (astProbe (bytesPay rivestDec)) .trap oa Rhos ⊆
      firstLeaves (Fam.Atom .rivest) :=
  ast_sound P _ hoa Rhos

theorem rivest_astR_live (P : Profile) (oa : OnInvalid) :
    leafNode rivestHi ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
        (astR (sexpSig (Fam.Atom .rivest)) (BitVec 32))
        (astProbe (bytesPay rivestDec)) .trap oa Set.univ :=
  pay_astR_live P oa rivestDec rivest_spec.hd

/-! ### Rivest hinted (`Fam.hinted`) -/

/-- **Rivest hinted, n-ary writer**:
`pairAtomMod "blob"` writes only `(hintedA hintedB)`. -/
theorem hinted_naryW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") hintedTab {} pol ⊆
      {SExp.ofList [.atom hintedA, .atom hintedB]} :=
  hinted_list.naryW_sound P hs hw ha

theorem hinted_naryW_live (P : Profile) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom hintedA, .atom hintedB] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") hintedTab {} pol :=
  hinted_list.naryW_live P pol

/-- **Rivest hinted, cons writer**:
`consAtomMod "blob"` writes only `(hintedHi)`. -/
theorem hinted_consW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "blob") hintedTab {} pol ⊆
      {.cons (.atom hintedHi) .nil} :=
  hinted_spec.consW_sound P hs hw ha

theorem hinted_consW_live (P : Profile) (pol : Policy (BitVec 32)) :
    .cons (.atom hintedHi) .nil ∈
      tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod "blob") hintedTab {} pol :=
  hinted_spec.consW_live P pol

/-- **Rivest hinted, AST writer**:
`pairAtomMod "blob"` writes only the branch with leaves `hintedA`, `hintedB`. -/
theorem hinted_astW_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") hintedTab {} pol ⊆
      {SExp.toAST (SExp.ofList [.atom hintedA, .atom hintedB])} :=
  (hinted_list.astW_lang P hs hw ha).subset

theorem hinted_astW_live (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    SExp.toAST (SExp.ofList [.atom hintedA, .atom hintedB]) ∈
      tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod "blob") hintedTab {}
        pol := by
  rw [hinted_list.astW_lang P hs hw ha]; rfl

/-- **Rivest hinted, n-ary reader**:
only lists whose first child is an atom. -/
theorem hinted_naryR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp (Fam.Atom .hinted)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR (Fam.Atom .hinted) (BitVec 32))
      (naryProbe (bytesPay hintedDec)) .trap oa Rhos ⊆
      firstAtoms (Fam.Atom .hinted) :=
  nary_sound P _ hoa Rhos

theorem hinted_naryR_live (P : Profile) (oa : OnInvalid) :
    SExp.ofList [.atom hintedHi] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
        (sexpR (Fam.Atom .hinted) (BitVec 32))
        (naryProbe (bytesPay hintedDec)) .trap oa Set.univ :=
  pay_naryR_live P oa hintedDec hinted_spec.hd

/-- **Rivest hinted, cons reader**:
only pairs whose car is an atom. -/
theorem hinted_consR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (SExp2 (Fam.Atom .hinted)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR (Fam.Atom .hinted) (BitVec 32))
      (consProbe (bytesPay hintedDec)) .trap oa Rhos ⊆
      carAtoms (Fam.Atom .hinted) :=
  cons_sound P _ hoa Rhos

theorem hinted_consR_live (P : Profile) (oa : OnInvalid) :
    SExp2.cons (.atom hintedHi) .nil ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
        (consR (Fam.Atom .hinted) (BitVec 32))
        (consProbe (bytesPay hintedDec)) .trap oa Set.univ :=
  pay_consR_live P oa hintedDec hinted_spec.hd

/-- **Rivest hinted, AST reader**:
only nodes whose first child is a leaf. -/
theorem hinted_astR_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (HEnv (BitVec 32) (AST (sexpSig (Fam.Atom .hinted))))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig (Fam.Atom .hinted)) (BitVec 32))
      (astProbe (bytesPay hintedDec)) .trap oa Rhos ⊆
      firstLeaves (Fam.Atom .hinted) :=
  ast_sound P _ hoa Rhos

theorem hinted_astR_live (P : Profile) (oa : OnInvalid) :
    leafNode hintedHi ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
        (astR (sexpSig (Fam.Atom .hinted)) (BitVec 32))
        (astProbe (bytesPay hintedDec)) .trap oa Set.univ :=
  pay_astR_live P oa hintedDec hinted_spec.hd

end Silmaril.Wasm.Game.HandleAccept.Families
