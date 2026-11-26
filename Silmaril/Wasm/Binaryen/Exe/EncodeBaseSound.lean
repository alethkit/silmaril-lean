module

public import Silmaril.Parse.Binary.Thms
public import Silmaril.Wasm.Binaryen.Exe.EncodeBase
public import Silmaril.Wasm.Binaryen.Exe.ExceptSound
public import Silmaril.Wasm.Binary.Core.Modules

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

/-! ## `Except` plumbing -/

theorem throw_ne_ok {ε α : Type} {e : ε} {b : α} : (throw e : Except ε α) ≠ .ok b := by
  intro h
  cases h

/-! ## LEB128 -/

export Silmaril.Parse.Binary (encU_sound encS_sound)

theorem encU32_sound {n : Nat} {b : List UInt8} (h : encU32 n = .ok b) : U32 b n := by
  unfold encU32 at h
  split at h
  · next hn =>
    cases Except.ok.inj h
    exact encU_sound hn
  · exact absurd h throw_ne_ok

theorem encIdx_sound {k : IndexKind} (x : Idx k) : Index (encIdx x) x :=
  encU_sound x.value.isLt

/-- An `iN` constant: signed LEB128 of the two's-complement value. -/
theorem in_toInt {w : Nat} (hw : 0 < w) (b : BitVec w) : IN w (encS b.toInt) b := by
  have := IN.mk (encS_sound (N := w) (BitVec.le_toInt b) BitVec.toInt_lt hw)
  rwa [BitVec.ofInt_toInt] at this

/-! ## Vectors, sections, names -/

theorem encList_sound {α β : Type} {f : α → Except String (List UInt8)}
    {G : Bytes → β → Prop} {g : α → β} :
    ∀ {xs : List α} {bs : List UInt8}, (∀ x ∈ xs, ∀ b, f x = .ok b → G b (g x)) →
      encList f xs = .ok bs → Seq G bs (xs.map g)
  | [], bs, _, h => by
    simp only [encList] at h
    cases Except.ok.inj h
    exact Seq.nil
  | x :: xs, bs, hf, h => by
    simp only [encList] at h
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact Seq.cons (hf x List.mem_cons_self a ha)
      (encList_sound (fun y hy => hf y (List.mem_cons_of_mem _ hy)) hb)

theorem encVec_sound {α β : Type} {f : α → Except String (List UInt8)}
    {G : Bytes → β → Prop} {g : α → β} {xs : List α} {bs : List UInt8}
    (hf : ∀ x ∈ xs, ∀ b, f x = .ok b → G b (g x)) (h : encVec f xs = .ok bs) :
    Vec G bs (xs.map g) := by
  unfold encVec at h
  obtain ⟨a, ha, h⟩ := bind_ok h
  obtain ⟨b, hb, h⟩ := bind_ok h
  cases Except.ok.inj h
  exact Vec.mk (by rw [List.length_map]; exact encU32_sound ha) (encList_sound hf hb)

theorem encVec_sound_id {α : Type} {f : α → Except String (List UInt8)}
    {G : Bytes → α → Prop} {xs : List α} {bs : List UInt8}
    (hf : ∀ x ∈ xs, ∀ b, f x = .ok b → G b x) (h : encVec f xs = .ok bs) : Vec G bs xs := by
  have := encVec_sound (g := id) hf h
  rwa [List.map_id] at this

theorem encSection_sound {α : Type} {G : Bytes → List α → Prop} {n : UInt8} {count : Nat}
    {body bs : List UInt8} {xs : List α} (hG : count ≠ 0 → G body xs)
    (hc : count = 0 → xs = []) (h : encSection n count body = .ok bs) : Section n G bs xs := by
  unfold encSection at h
  split at h
  · next h0 =>
    cases Except.ok.inj h
    rw [hc h0]
    exact Section.empty
  · next h0 =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact Section.mk (encU32_sound ha) rfl (hG h0)

theorem seq_byte : ∀ bs : List UInt8, Seq Byte bs bs
  | [] => Seq.nil
  | b :: bs => Seq.cons (Byte.mk b) (seq_byte bs)

theorem encName_sound {s : String} {bs : List UInt8} (h : encName s = .ok bs) : Name bs s := by
  unfold encName at h
  obtain ⟨a, ha, h⟩ := bind_ok h
  cases Except.ok.inj h
  exact Name.mk (Vec.mk (encU32_sound ha) (seq_byte _)) (Utf8.toUTF8 s)

end Silmaril.Wasm.Binaryen.Exe
