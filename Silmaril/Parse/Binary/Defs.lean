module

/-! # Generic binary grammar primitives and LEB128 encoders

Byte-level relational grammars (`Bytes`, `Byte`, `UN`, `SN`, `IN`, `FN`, `Seq`,
`Vec`, `ByteVec`, `Utf8`, `Name`) and minimal LEB128 encoders (`encU`, `encS`),
shared by `Silmaril.Parse.ByteParse`, `Silmaril.Wasm.Binary`, and other binary
formats.

Every production is a relation `G : Bytes → α → Prop` on the *exact* byte string
it generates; sequencing is list concatenation.
-/

@[expose] public section

namespace Silmaril.Parse.Binary

/-- Byte strings, the terminals of the grammar. -/
abbrev Bytes := List UInt8

/-! ## Unambiguity -/

/-- No encoding is a proper prefix of another, and equal encodings agree on the
syntax: the parse of a production is determined by any byte string it begins. -/
def PrefixFree {α : Type} (G : Bytes → α → Prop) : Prop :=
  ∀ ⦃b b' r r' : Bytes⦄ ⦃a a' : α⦄, G b a → G b' a' → b ++ r = b' ++ r' → b = b' ∧ a = a'

/-- A byte string encodes at most one value. -/
def Functional {α : Type} (G : Bytes → α → Prop) : Prop :=
  ∀ ⦃b : Bytes⦄ ⦃a a' : α⦄, G b a → G b a' → a = a'

theorem PrefixFree.functional {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G) :
    Functional G :=
  fun _ _ _ ha ha' => (h (r := []) (r' := []) ha ha' rfl).2

/-! ## Bytes -/

/-- Single byte production: `byte = 0x00 | … | 0xFF`. -/
inductive Byte : Bytes → UInt8 → Prop where
  | mk (b : UInt8) : Byte [b] b

theorem Byte.prefixFree : PrefixFree Byte := by
  rintro _ _ r r' _ _ ⟨b⟩ ⟨b'⟩ h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  exact ⟨by rw [h.1], h.1⟩

/-! ## LEB128 integers -/

/-- Unsigned LEB128 bounded to `N` bits:

* `n:Bbyte => n` if `n < 2^7 ∧ n < 2^N`;
* `n:Bbyte m:BuN(N-7) => 2^7 * m + (n - 2^7)` if `n ≥ 2^7 ∧ N > 7`.

Non-minimal encodings are allowed up to `⌈N/7⌉` bytes; the bound on the final
byte forces its unused high bits to be zero. -/
inductive UN : Nat → Bytes → Nat → Prop where
  | byte {N : Nat} (n : UInt8) (h₁ : n.toNat < 2 ^ 7) (h₂ : n.toNat < 2 ^ N) :
      UN N [n] n.toNat
  | cont {N : Nat} (n : UInt8) {b : Bytes} {m : Nat} (h₁ : 2 ^ 7 ≤ n.toNat) (h₂ : 7 < N)
      (rest : UN (N - 7) b m) : UN N (n :: b) (2 ^ 7 * m + (n.toNat - 2 ^ 7))

/-- Unsigned 32-bit LEB128 (`UN 32`). -/
abbrev U32 := UN 32
/-- Unsigned 64-bit LEB128 (`UN 64`). -/
abbrev U64 := UN 64

/-- Signed LEB128 bounded to `N` bits:

* `n:Bbyte => n` if `n < 2^6 ∧ n < 2^(N-1)`;
* `n:Bbyte => n - 2^7` if `2^6 ≤ n < 2^7 ∧ n ≥ 2^7 - 2^(N-1)`;
* `n:Bbyte i:BsN(N-7) => 2^7 * i + (n - 2^7)` if `n ≥ 2^7 ∧ N > 7`. -/
inductive SN : Nat → Bytes → Int → Prop where
  | pos {N : Nat} (n : UInt8) (h₁ : n.toNat < 2 ^ 6) (h₂ : n.toNat < 2 ^ (N - 1)) :
      SN N [n] n.toNat
  | neg {N : Nat} (n : UInt8) (h₁ : 2 ^ 6 ≤ n.toNat) (h₂ : n.toNat < 2 ^ 7)
      (h₃ : (2 : Int) ^ 7 - 2 ^ (N - 1) ≤ n.toNat) : SN N [n] ((n.toNat : Int) - 2 ^ 7)
  | cont {N : Nat} (n : UInt8) {b : Bytes} {i : Int} (h₁ : 2 ^ 7 ≤ n.toNat) (h₂ : 7 < N)
      (rest : SN (N - 7) b i) : SN N (n :: b) (2 ^ 7 * i + ((n.toNat : Int) - 2 ^ 7))

/-- Signed 33-bit LEB128 (`SN 33`). -/
abbrev S33 := SN 33

/-- Uninterpreted integers: signed LEB128, stored as their two's-complement bit pattern. -/
inductive IN (N : Nat) : Bytes → BitVec N → Prop where
  | mk {b : Bytes} {i : Int} (h : SN N b i) : IN N b (BitVec.ofInt N i)

/-- Unsigned LEB128 encoder, minimal. -/
def encU (n : Nat) : List UInt8 :=
  if h : n < 0x80 then [UInt8.ofNat n]
  else UInt8.ofNat (n % 0x80 + 0x80) :: encU (n / 0x80)
termination_by n
decreasing_by omega

/-- Signed LEB128 encoder, minimal. -/
def encS (i : Int) : List UInt8 :=
  if h : -64 ≤ i ∧ i < 64 then [UInt8.ofNat (i % 128).toNat]
  else UInt8.ofNat (i % 128 + 128).toNat :: encS (i / 128)
termination_by i.natAbs
decreasing_by omega

/-! ## Floating point / little-endian -/

/-- The little-endian value of a byte string. -/
def littleEndian : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 ^ 8 * littleEndian bs

/-- IEEE 754 bit pattern in little-endian byte order. -/
inductive FN (N : Nat) : Bytes → BitVec N → Prop where
  | mk (b : Bytes) (h : b.length = N / 8) : FN N b (BitVec.ofNat N (littleEndian b))

/-! ## Sequences and vectors -/

/-- `(x:B)*`: a concatenation of encodings, one per element. -/
inductive Seq {α : Type} (G : Bytes → α → Prop) : Bytes → List α → Prop where
  | nil : Seq G [] []
  | cons {b bs : Bytes} {a : α} {as : List α} : G b a → Seq G bs as → Seq G (b ++ bs) (a :: as)

/-- Length-prefixed vector: `n:Bu32 (el:BX)^n => el^n`. -/
inductive Vec {α : Type} (G : Bytes → α → Prop) : Bytes → List α → Prop where
  | mk {n b : Bytes} {xs : List α} : U32 n xs.length → Seq G b xs → Vec G (n ++ b) xs

/-- A byte vector `Vec Byte`. -/
abbrev ByteVec := Vec Byte

/-! ## UTF-8 and names -/

/-- A UTF-8 continuation byte (`0x80 ≤ b < 0xC0`). -/
def IsCont (b : UInt8) : Prop := 0x80 ≤ b.toNat ∧ b.toNat < 0xC0

/-- UTF-8 encoding as a relation between a scalar value and its bytes. -/
inductive Utf8Char : Char → Bytes → Prop where
  | one {c : Char} (b : UInt8) (h : c.toNat < 0x80) (e : c.toNat = b.toNat) : Utf8Char c [b]
  | two {c : Char} (b₁ b₂ : UInt8) (lo : 0x80 ≤ c.toNat) (hi : c.toNat < 0x800)
      (h₁ : 0xC0 ≤ b₁.toNat) (h₂ : IsCont b₂)
      (e : c.toNat = 2 ^ 6 * (b₁.toNat - 0xC0) + (b₂.toNat - 0x80)) : Utf8Char c [b₁, b₂]
  | three {c : Char} (b₁ b₂ b₃ : UInt8)
      (range : 0x800 ≤ c.toNat ∧ c.toNat < 0xD800 ∨ 0xE000 ≤ c.toNat ∧ c.toNat < 0x10000)
      (h₁ : 0xE0 ≤ b₁.toNat) (h₂ : IsCont b₂) (h₃ : IsCont b₃)
      (e : c.toNat = 2 ^ 12 * (b₁.toNat - 0xE0) + 2 ^ 6 * (b₂.toNat - 0x80) + (b₃.toNat - 0x80)) :
      Utf8Char c [b₁, b₂, b₃]
  | four {c : Char} (b₁ b₂ b₃ b₄ : UInt8) (lo : 0x10000 ≤ c.toNat) (hi : c.toNat < 0x110000)
      (h₁ : 0xF0 ≤ b₁.toNat) (h₂ : IsCont b₂) (h₃ : IsCont b₃) (h₄ : IsCont b₄)
      (e : c.toNat = 2 ^ 18 * (b₁.toNat - 0xF0) + 2 ^ 12 * (b₂.toNat - 0x80) +
        2 ^ 6 * (b₃.toNat - 0x80) + (b₄.toNat - 0x80)) :
      Utf8Char c [b₁, b₂, b₃, b₄]

/-- UTF-8 byte sequence for a list of scalar values. -/
def Utf8 (cs : List Char) (b : Bytes) : Prop := Seq (fun b c => Utf8Char c b) b cs

/-- Length-prefixed UTF-8 string. -/
inductive Name : Bytes → String → Prop where
  | mk {b : Bytes} {bs : List UInt8} {s : String} (v : ByteVec b bs) (u : Utf8 s.toList bs) :
      Name b s

end Silmaril.Parse.Binary
