module

public import Silmaril.Parse.Binary.Thms
public import Silmaril.Wasm.Types

/-! # Shared WebAssembly binary grammar

Productions common to the Wasm 1.0 Recommendation (2019, chapter 5) and the
Core 3.0 SpecTec grammar (`5.1-binary.values.spectec`, `5.4-binary.modules.spectec`):
bytes, LEB128 integers with a bit-width bound, IEEE floats, vectors, names,
indices, sections and custom sections.

The format-independent byte, LEB128, sequence, vector and UTF-8 primitives live
in `Silmaril.Parse.Binary` and are re-exported here under `Silmaril.Wasm.Binary`.
Wasm-specific productions (`Index`, `Section`, `Custom`, `CustomSec`, `Customs`,
`Start`, `StartSec`, `magic`, `version`) are defined below.

Every production is a relation `G : Bytes → α → Prop` on the *exact* byte string
it generates; sequencing is list concatenation, as in the attribute grammars of
both specifications. Citations `5.1:n` refer to line `n` of
`5.1-binary.values.spectec`, and `REC 5.x.y` to the 2019 Recommendation.

## Deviations from the pinned SpecTec source (errata)

* `$cont(b)` is defined for `0x80 ≤ b < 0xC0`. SpecTec (5.1:49) writes
  `0x80 < b < 0xC0`, which would make e.g. `U+0080` (`C2 80`) unencodable; the
  Recommendation (REC 5.2.4: `b₂,b₃,b₄ < 0xC0` with `bᵢ - 0x80`) and Unicode agree
  with the inclusive bound.
* The four-byte UTF-8 range is `U+10000 ≤ c < U+110000`. SpecTec (5.1:63) writes
  `U+11000`, an evident typo (REC 5.2.4 has `U+110000`).
* `Bi32`/`Bi64` (uninterpreted integers) are `BiN`, i.e. *signed* LEB128 (`IN`
  below). The pinned SpecTec (5.1:31–32) writes `Bi32 = BuN(32)`, leaving `BiN`
  unused; this contradicts REC 5.2.2 ("uninterpreted integers are encoded as
  signed integers") and every implementation (`i32.const -1` is `41 7F`).

All three were independently re-verified against the pinned file (SHA-256 matches
`specs/wasm/core-3.0.json`), SpecTec's elaboration, the reference interpreter and the
test suite. These checks describe the pinned source revision.

## Agreement with the reference interpreter

The integer and name productions accept exactly the bytes that the official reference
interpreter (`WebAssembly/spec@6087111…`, `interpreter/binary/decode.ml` and `utf8.ml`)
accepts, with the same values. `Silmaril.Wasm.Binary.RefInterp` transcribes those
decoders line by line and proves, for every width `N > 0`:

* `RefInterp.utf8_iff : Utf8 cs b ↔ refUtf8Decode b = some cs`;
* `RefInterp.name_iff : Name b s ↔ refName b = some (s.toList, [])`;
* `RefInterp.un_iff : UN N b n ↔ refUN N b = some (n, [])`, likewise `sn_iff` and `in_iff`
  (with `u32_iff`, `u64_iff`, `s32_iff`, `s33_iff`, `s64_iff`, `i32_iff`, `i64_iff`), and
  the consumed-prefix forms `refUN_eq_some_iff`, `refSN_eq_some_iff`, `refIN_eq_some_iff`,
  `refName_eq_some_iff`.

The UTF-8 leading-byte bounds (`0xC0 ≤ b₁`, `0xE0 ≤ b₁`, `0xF0 ≤ b₁`) are SpecTec's
partial subtraction `b₁ - 0xC0` made explicit, and are needed for `utf8_iff`: without
`0xE0 ≤ b₁`, truncated subtraction would accept `00 A0 80` as `U+0800`.
-/

@[expose] public section

namespace Silmaril.Wasm.Binary

export Silmaril.Parse.Binary (
  Bytes PrefixFree Functional
  Byte UN U32 U64 SN S33 IN
  littleEndian FN
  Seq Vec ByteVec
  IsCont Utf8Char Utf8 Name
)

namespace PrefixFree
export Silmaril.Parse.Binary.PrefixFree (functional cancel)
end PrefixFree

namespace Byte
export Silmaril.Parse.Binary.Byte (mk prefixFree)
end Byte

namespace UN
export Silmaril.Parse.Binary.UN (
  byte cont ne_nil head_lt lt_two_pow length_le mono exists_of_lt prefixFree functional u32_zero_iff
)
end UN

namespace SN
export Silmaril.Parse.Binary.SN (
  pos neg cont bounds length_le mono prefixFree functional
)
end SN

namespace IN
export Silmaril.Parse.Binary.IN (mk prefixFree)
end IN

namespace FN
export Silmaril.Parse.Binary.FN (mk prefixFree)
end FN

namespace Seq
export Silmaril.Parse.Binary.Seq (nil cons functional imp)
end Seq

namespace Vec
export Silmaril.Parse.Binary.Vec (mk prefixFree imp)
end Vec

namespace Utf8Char
export Silmaril.Parse.Binary.Utf8Char (one two three four)
end Utf8Char

namespace Utf8
export Silmaril.Parse.Binary.Utf8 (functional toUTF8)
end Utf8

namespace Name
export Silmaril.Parse.Binary.Name (mk prefixFree)
end Name

/-! ## Indices (5.1:72–82, REC 5.5.1) -/

/-- Every index production is `x:Bu32 => x`. -/
def Index {k : IndexKind} (b : Bytes) (x : Idx k) : Prop := U32 b x.toNat

/-! ## Sections (5.4:9–11, REC 5.5.2) -/

/-- `Bsection_(N, BX) : en* = N:Bbyte len:Bu32 en*:BX => en* -- if len = ||BX|| | eps => eps`. -/
inductive Section {α : Type} (N : UInt8) (G : Bytes → List α → Prop) : Bytes → List α → Prop where
  | mk {lb c : Bytes} {len : Nat} {xs : List α} (hl : U32 lb len) (hlen : len = c.length)
      (hc : G c xs) : Section N G ([N] ++ lb ++ c) xs
  | empty : Section N G [] []

/-- `Bcustom : ()* = Bname Bbyte* => ()` (5.4:16–17; REC 5.5.3 `custom ::= name byte*`). -/
inductive Custom : Bytes → List Unit → Prop where
  | mk {bn : Bytes} {nm : String} (rest : Bytes) (h : Name bn nm) : Custom (bn ++ rest) [()]

/-- `Bcustomsec : () = Bsection_(0, Bcustom) => ()` (5.4:19–20). -/
def CustomSec (b : Bytes) : Prop := ∃ xs, Section 0 Custom b xs

/-- `Bcustomsec*`: any number of custom sections, ignored by the abstract syntax. -/
inductive Customs : Bytes → Prop where
  | nil : Customs []
  | cons {b bs : Bytes} : CustomSec b → Customs bs → Customs (b ++ bs)

/-- `Bstart : start* = x:Bfuncidx => (START x)` (5.4:86–87; REC 5.5.11 `start ::= x:funcidx`). -/
inductive Start : Bytes → List FuncIdx → Prop where
  | mk {b : Bytes} {x : FuncIdx} (h : Index b x) : Start b [x]

/-- `Bstartsec : start? = startopt:Bsection_(8, Bstart) => $opt_(start, startopt)` (5.4:91–92). -/
inductive StartSec : Bytes → Option FuncIdx → Prop where
  | mk {b : Bytes} {xs : List FuncIdx} (h : Section 8 Start b xs) : StartSec b xs.head?

/-- The magic number `\0asm` (5.4:173, REC 5.5.15). -/
def magic : Bytes := [0x00, 0x61, 0x73, 0x6D]

/-- The version field `1` (5.4:174, REC 5.5.15). -/
def version : Bytes := [0x01, 0x00, 0x00, 0x00]

theorem Index.prefixFree {k : IndexKind} : PrefixFree (Index (k := k)) := by
  intro _ _ _ _ x x' h h' he
  obtain ⟨rfl, hx⟩ := UN.prefixFree 32 h h' he
  refine ⟨rfl, ?_⟩
  cases x
  cases x'
  simp only [Idx.toNat] at hx
  exact congrArg Idx.mk (Fin.ext hx)

end Silmaril.Wasm.Binary
