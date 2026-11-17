module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules

/-!
# Proofs: decoding payload values through memory

* `le32_encode`, `readPtrLen_encode`: a `(ptr, len)` pair written as two little-endian `i32`s
  is read back;
* `readPtrLen_rest`, `readVal_rest`: **a payload value consumes exactly `PTy.width t` bytes** of
  the payload area (so a payload vector is packed);
* `readVal_string`, `readVal_bytes`, `readVal_list`: the indirect values from their pair, the
  memory segment it names and (for strings) its UTF-8 decoding, (for lists) its elements.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Formats Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

theorem length_encode4 (v : Nat) : (Memory.encodeLE 4 v).data.toList.length = 4 := by
  rw [Array.length_toList]
  exact Memory.encodeLE_size 4 v

theorem le32_encode (r : BitVec 32) : le32 (Memory.encodeLE 4 r.toNat).data.toList = some r := by
  unfold le32
  rw [← List.append_nil (Memory.encodeLE 4 r.toNat).data.toList, le32s_encode]
  rfl

/-- **A `(ptr, len)` pair is read back.** -/
theorem readPtrLen_encode (p n : BitVec 32) (rest : List UInt8) :
    readPtrLen ((Memory.encodeLE 4 p.toNat).data.toList ++ (Memory.encodeLE 4 n.toNat).data.toList
      ++ rest) = some (p.toNat, n.toNat, rest) := by
  have hp := length_encode4 p.toNat
  have hn := length_encode4 n.toNat
  unfold readPtrLen
  rw [List.append_assoc, List.take_left' hp, le32_encode, List.drop_left' hp,
    List.take_left' hn, le32_encode]
  simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
  rw [show 8 = 4 + 4 from rfl, ← List.drop_drop, List.drop_left' hp, List.drop_left' hn]

/-- A pair leaves the payload area after its eight bytes. -/
theorem readPtrLen_rest {bs rest : List UInt8} {p n : Nat}
    (h : readPtrLen bs = some (p, n, rest)) : rest = bs.drop 8 := by
  unfold readPtrLen at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨_, -, _, -, -, -, rfl⟩ := h
  rfl

/-- **A payload value consumes exactly its width.** -/
theorem readVal_rest {seg : Nat → Nat → Option (List UInt8)} :
    ∀ {t : PTy} {bs rest : List UInt8} {v : t.Val},
      readVal seg t bs = some (v, rest) → rest = bs.drop (PTy.width t)
  | .bool, b :: bs, rest, v, h => by
    simp only [readVal] at h
    exact (congrArg Prod.snd (Option.some.inj h)).symm
  | .bool, [], _, _, h => by simp [readVal] at h
  | .s32, bs, rest, v, h => by
    simp only [readVal, Option.map_eq_some_iff] at h
    obtain ⟨_, -, h⟩ := h
    exact (congrArg Prod.snd h).symm
  | .u32, bs, rest, v, h => by
    simp only [readVal, Option.map_eq_some_iff] at h
    obtain ⟨_, -, h⟩ := h
    exact (congrArg Prod.snd h).symm
  | .s64, bs, rest, v, h => by
    simp only [readVal, Option.map_eq_some_iff] at h
    obtain ⟨_, -, h⟩ := h
    exact (congrArg Prod.snd h).symm
  | .u64, bs, rest, v, h => by
    simp only [readVal, Option.map_eq_some_iff] at h
    obtain ⟨_, -, h⟩ := h
    exact (congrArg Prod.snd h).symm
  | .string, bs, rest, v, h => by
    rcases hp : readPtrLen bs with _ | ⟨p, n, r⟩
    · simp [readVal, hp] at h
    · simp only [readVal, hp, Option.bind_some] at h
      rcases hc : seg p n with _ | cs
      · simp [hc] at h
      · rcases hu : utf8? cs with _ | str
        · simp only [hc, hu, Option.bind_some] at h
          cases h
        · simp only [hc, hu, Option.bind_some] at h
          have e : r = rest := congrArg Prod.snd (Option.some.inj h)
          rw [← e]; exact readPtrLen_rest hp
  | .bytes, bs, rest, v, h => by
    rcases hp : readPtrLen bs with _ | ⟨p, n, r⟩
    · simp [readVal, hp] at h
    · simp only [readVal, hp, Option.bind_some] at h
      rcases hc : seg p n with _ | cs
      · simp only [hc] at h
        cases h
      · simp only [hc] at h
        have e : r = rest := congrArg Prod.snd (Option.some.inj h)
        rw [← e]; exact readPtrLen_rest hp
  | .list t, bs, rest, v, h => by
    rcases hp : readPtrLen bs with _ | ⟨p, n, r⟩
    · simp [readVal, hp] at h
    · simp only [readVal, hp, Option.bind_some] at h
      rcases hc : seg p (n * PTy.width t) with _ | es
      · simp [hc] at h
      · simp only [hc, Option.bind_some] at h
        rcases hm : readMany (readVal seg t) n es with _ | ⟨vs, r'⟩
        · simp [hm] at h
        · simp only [hm, Option.bind_some] at h
          split at h
          · have e : r = rest := congrArg Prod.snd (Option.some.inj h)
            rw [← e]; exact readPtrLen_rest hp
          · cases h

/-- **A string payload**: its pair, the segment it names, the UTF-8 text. -/
theorem readVal_string {seg : Nat → Nat → Option (List UInt8)} {bs rest cs : List UInt8}
    {p n : Nat} {str : String} (hp : readPtrLen bs = some (p, n, rest))
    (hc : seg p n = some cs) (hu : utf8? cs = some str) :
    readVal seg .string bs = some (str, rest) := by
  simp only [readVal, hp, Option.bind_some, hc, hu]
  rfl

/-- **A byte-string payload**: its pair and the segment it names. -/
theorem readVal_bytes {seg : Nat → Nat → Option (List UInt8)} {bs rest cs : List UInt8}
    {p n : Nat} (hp : readPtrLen bs = some (p, n, rest)) (hc : seg p n = some cs) :
    readVal seg .bytes bs = some (cs, rest) := by
  simp only [readVal, hp, Option.bind_some, hc]
  rfl

/-- **A list payload**: its pair, the segment of `len` packed elements, the elements. -/
theorem readVal_list {seg : Nat → Nat → Option (List UInt8)} {t : PTy}
    {bs rest es : List UInt8} {p n : Nat} {vs : List t.Val}
    (hp : readPtrLen bs = some (p, n, rest)) (hc : seg p (n * PTy.width t) = some es)
    (hm : readMany (readVal seg t) n es = some (vs, [])) :
    readVal seg (.list t) bs = some (vs, rest) := by
  simp only [readVal, hp, Option.bind_some, hc, hm, List.isEmpty_nil, ↓reduceIte]
  rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst
