module

public import Silmaril.Parse.Binary.Defs
import Silmaril.Proofs.Parse.Binary.Basic

/-! # Theorems for generic binary grammar primitives and LEB128 encoders -/

@[expose] public section

namespace Silmaril.Parse.Binary

namespace UN

/-- No `UN` encoding is empty. -/
theorem ne_nil {N : Nat} {v : Nat} (h : UN N [] v) : False :=
  Silmaril.Proofs.Parse.Binary.UN.ne_nil h

/-- A byte below `2^7` ends an encoding. -/
theorem head_lt {N : Nat} {n : UInt8} {b : Bytes} {v : Nat} (h : UN N (n :: b) v)
    (hn : n.toNat < 2 ^ 7) : b = [] ∧ v = n.toNat :=
  Silmaril.Proofs.Parse.Binary.UN.head_lt h hn

theorem lt_two_pow {N : Nat} {b : Bytes} {v : Nat} (h : UN N b v) : v < 2 ^ N :=
  Silmaril.Proofs.Parse.Binary.UN.lt_two_pow h

/-- At most `⌈N/7⌉` bytes. The hypothesis `0 < N` is needed: `UN 0 [0x00] 0` holds. -/
theorem length_le {N : Nat} (hN : 0 < N) {b : Bytes} {v : Nat} (h : UN N b v) :
    b.length ≤ (N + 6) / 7 :=
  Silmaril.Proofs.Parse.Binary.UN.length_le hN h

/-- A narrower encoding is also a wider one; e.g. every `u32` encoding is a `u64` encoding
of the same value. The converse fails (`u64` admits up to ten bytes). -/
theorem mono {N M : Nat} (hNM : N ≤ M) {b : Bytes} {v : Nat} (h : UN N b v) : UN M b v :=
  Silmaril.Proofs.Parse.Binary.UN.mono hNM h

/-- Every in-range value has an encoding (the minimal one). -/
theorem exists_of_lt {N v : Nat} (hN : 0 < N) (hv : v < 2 ^ N) : ∃ b, UN N b v :=
  Silmaril.Proofs.Parse.Binary.UN.exists_of_lt hN hv

theorem prefixFree (N : Nat) : PrefixFree (UN N) :=
  Silmaril.Proofs.Parse.Binary.UN.prefixFree N

theorem functional (N : Nat) : Functional (UN N) :=
  Silmaril.Proofs.Parse.Binary.UN.functional N

/-- The `u32` encodings of zero are `0x80^k 0x00` with `k ≤ 4`. -/
theorem u32_zero_iff (b : Bytes) :
    U32 b 0 ↔ ∃ k, k ≤ 4 ∧ b = List.replicate k 0x80 ++ [0x00] :=
  Silmaril.Proofs.Parse.Binary.UN.u32_zero_iff b

end UN

namespace SN

theorem bounds {N : Nat} {b : Bytes} {i : Int} (h : SN N b i) :
    -(2 : Int) ^ (N - 1) ≤ i ∧ i < 2 ^ (N - 1) :=
  Silmaril.Proofs.Parse.Binary.SN.bounds h

/-- At most `⌈N/7⌉` bytes. The hypothesis `0 < N` is needed: `SN 0 [0x00] 0` holds
(`2 ^ (0 - 1) = 1` in `Nat`). -/
theorem length_le {N : Nat} (hN : 0 < N) {b : Bytes} {i : Int} (h : SN N b i) :
    b.length ≤ (N + 6) / 7 :=
  Silmaril.Proofs.Parse.Binary.SN.length_le hN h

theorem mono {N M : Nat} (hNM : N ≤ M) {b : Bytes} {i : Int} (h : SN N b i) : SN M b i :=
  Silmaril.Proofs.Parse.Binary.SN.mono hNM h

theorem prefixFree (N : Nat) : PrefixFree (SN N) :=
  Silmaril.Proofs.Parse.Binary.SN.prefixFree N

theorem functional (N : Nat) : Functional (SN N) :=
  Silmaril.Proofs.Parse.Binary.SN.functional N

end SN

theorem IN.prefixFree (N : Nat) : PrefixFree (IN N) :=
  Silmaril.Proofs.Parse.Binary.IN.prefixFree N

theorem FN.prefixFree (N : Nat) : PrefixFree (FN N) :=
  Silmaril.Proofs.Parse.Binary.FN.prefixFree N

/-- Cancel a prefix-free production at the front of two equal byte strings. -/
theorem PrefixFree.cancel {α : Type} {G : Bytes → α → Prop}
    (hG : PrefixFree G) {b b' r r' : Bytes} {a a' : α} (h : G b a) (h' : G b' a')
    (e : b ++ r = b' ++ r') : b = b' ∧ a = a' ∧ r = r' := by
  obtain ⟨rfl, rfl⟩ := hG h h' e
  exact ⟨rfl, rfl, List.append_cancel_left e⟩

/-- A sequence of a prefix-free production with no empty encoding is functional.
The hypothesis `hne` is needed: for `G b () := b = []`, `Seq G [] []` and
`Seq G [] [()]` both hold. (`Vec.prefixFree` needs no such hypothesis, since the
count is fixed.) -/
theorem Seq.functional {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G)
    (hne : ∀ a, ¬ G [] a) : Functional (Seq G) :=
  Silmaril.Proofs.Parse.Binary.Seq.functional h hne

/-- Weaken the element production of a sequence, on encodings no longer than the sequence. -/
theorem Seq.imp {α : Type} {G G' : Bytes → α → Prop} {b : Bytes}
    {xs : List α} (h : Seq G b xs) (hg : ∀ {c x}, c.length ≤ b.length → G c x → G' c x) :
    Seq G' b xs :=
  Silmaril.Proofs.Parse.Binary.Seq.imp h hg

theorem Vec.prefixFree {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G) :
    PrefixFree (Vec G) :=
  Silmaril.Proofs.Parse.Binary.Vec.prefixFree h

theorem Vec.imp {α : Type} {G G' : Bytes → α → Prop} {b : Bytes}
    {xs : List α} (h : Vec G b xs) (hg : ∀ {c x}, G c x → G' c x) : Vec G' b xs := by
  obtain ⟨hn, hs⟩ := h
  exact .mk hn (hs.imp fun _ hx => hg hx)

theorem Utf8.functional : Functional (fun b (s : List Char) => Utf8 s b) :=
  Silmaril.Proofs.Parse.Binary.Utf8.functional

/-- The specification's UTF-8 relation agrees with Lean's encoder. -/
theorem Utf8.toUTF8 (s : String) : Utf8 s.toList s.toUTF8.data.toList :=
  Silmaril.Proofs.Parse.Binary.Utf8.toUTF8 s

theorem Name.prefixFree : PrefixFree Name :=
  Silmaril.Proofs.Parse.Binary.Name.prefixFree

theorem encU_sound {N n : Nat} (h : n < 2 ^ N) : UN N (encU n) n :=
  Silmaril.Proofs.Parse.Binary.encU_sound h

theorem encS_sound {N : Nat} {i : Int} (hlo : -(2 ^ (N - 1) : Int) ≤ i)
    (hhi : i < 2 ^ (N - 1)) (hN : 0 < N) : SN N (encS i) i :=
  Silmaril.Proofs.Parse.Binary.encS_sound hlo hhi hN

end Silmaril.Parse.Binary
