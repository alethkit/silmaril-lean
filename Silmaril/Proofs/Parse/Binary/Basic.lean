module

public import Silmaril.Parse.Binary.Defs

/-! # Proofs for generic binary grammar primitives and LEB128 encoders -/

@[expose] public section

namespace Silmaril.Proofs.Parse.Binary

open Silmaril.Parse.Binary

private theorem u8_toNat {k : Nat} (hk : k < 256) : (UInt8.ofNat k).toNat = k :=
  UInt8.toNat_ofNat_of_lt' hk

/-! ## `UN` properties -/

namespace UN

theorem ne_nil {N : Nat} {v : Nat} (h : UN N [] v) : False := by
  cases h

theorem head_lt {N : Nat} {n : UInt8} {b : Bytes} {v : Nat} (h : UN N (n :: b) v)
    (hn : n.toNat < 2 ^ 7) : b = [] ∧ v = n.toNat := by
  cases h with
  | byte _ _ _ => exact ⟨rfl, rfl⟩
  | cont _ h₁ _ _ => omega

theorem lt_two_pow {N : Nat} {b : Bytes} {v : Nat} (h : UN N b v) : v < 2 ^ N := by
  induction h with
  | byte _ _ h₂ => exact h₂
  | @cont N n b m h₁ h₂ _ ih =>
    have hn := n.toNat_lt_size
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 7 := ⟨N - 7, by omega⟩
    simp only [Nat.add_sub_cancel] at ih
    rw [Nat.pow_add]
    simp only [Nat.reducePow, UInt8.size] at hn h₁ ⊢
    omega

theorem length_le {N : Nat} (hN : 0 < N) {b : Bytes} {v : Nat} (h : UN N b v) :
    b.length ≤ (N + 6) / 7 := by
  induction h with
  | byte => simp only [List.length_singleton]; omega
  | cont _ _ h₂ _ ih =>
    have := ih (by omega)
    simp only [List.length_cons]
    omega

theorem mono {N M : Nat} (hNM : N ≤ M) {b : Bytes} {v : Nat} (h : UN N b v) : UN M b v := by
  induction h generalizing M with
  | byte n h₁ h₂ => exact UN.byte n h₁ (Nat.lt_of_lt_of_le h₂ (Nat.pow_le_pow_right (by decide) hNM))
  | cont n h₁ h₂ _ ih => exact UN.cont n h₁ (by omega) (ih (by omega))

theorem exists_of_lt {N v : Nat} (hN : 0 < N) (hv : v < 2 ^ N) : ∃ b, UN N b v := by
  induction N using Nat.strongRecOn generalizing v with
  | ind N ih =>
  by_cases hs : v < 2 ^ 7
  · refine ⟨[UInt8.ofNat v], ?_⟩
    have hv' : (UInt8.ofNat v).toNat = v := by
      simp only [UInt8.toNat_ofNat', Nat.reducePow] at hs ⊢
      omega
    have := UN.byte (N := N) (UInt8.ofNat v) (by rw [hv']; exact hs) (by rw [hv']; exact hv)
    rwa [hv'] at this
  · have hN7 : 7 < N := by
      apply Nat.lt_of_not_le
      intro hc
      have := Nat.pow_le_pow_right (by decide : 0 < 2) hc
      omega
    obtain ⟨b, hb⟩ := ih (N - 7) (by omega) (v := v / 2 ^ 7) (by omega) (by
      rw [Nat.div_lt_iff_lt_mul (by decide), ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      exact hv)
    have hn : (UInt8.ofNat (v % 2 ^ 7 + 2 ^ 7)).toNat = v % 2 ^ 7 + 2 ^ 7 := by
      simp only [UInt8.toNat_ofNat', Nat.reducePow]
      omega
    refine ⟨UInt8.ofNat (v % 2 ^ 7 + 2 ^ 7) :: b, ?_⟩
    have := UN.cont (UInt8.ofNat (v % 2 ^ 7 + 2 ^ 7)) (by rw [hn]; omega) hN7 hb
    rw [hn] at this
    have heq : 2 ^ 7 * (v / 2 ^ 7) + (v % 2 ^ 7 + 2 ^ 7 - 2 ^ 7) = v := by
      simp only [Nat.reducePow]
      omega
    rwa [heq] at this

theorem prefixFree (N : Nat) : PrefixFree (UN N) := by
  intro b b' r r' a a' h h' he
  induction h generalizing b' r r' a' with
  | byte n h₁ _ =>
    cases b' with
    | nil => exact (ne_nil h').elim
    | cons n' b'' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨rfl, rfl⟩ := head_lt h' h₁
      exact ⟨rfl, rfl⟩
  | cont n h₁ _ _ ih =>
    cases h' with
    | byte n' h₁' _ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      omega
    | cont n' _ _ rest' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl⟩ := ih rest' he
      exact ⟨rfl, rfl⟩

theorem functional (N : Nat) : Functional (UN N) := (prefixFree N).functional

private theorem zero_shape {N : Nat} {b : Bytes} {v : Nat} (h : UN N b v) (hv : v = 0) :
    ∃ k, b = List.replicate k 0x80 ++ [0x00] := by
  induction h with
  | byte n _ _ =>
    refine ⟨0, ?_⟩
    have : n = 0 := UInt8.toNat_inj.mp (by rw [hv]; rfl)
    simp [this]
  | cont n h₁ _ _ ih =>
    obtain ⟨k, rfl⟩ := ih (by omega)
    refine ⟨k + 1, ?_⟩
    have : n = 0x80 := UInt8.toNat_inj.mp (by
      have := n.toNat_lt_size
      simp only [Nat.reducePow, UInt8.size] at this h₁ hv
      show n.toNat = 128
      omega)
    simp [this, List.replicate_succ]

private theorem zero_enc {N : Nat} (k : Nat) (hk : 7 * k < N) :
    UN N (List.replicate k 0x80 ++ [0x00]) 0 := by
  induction k generalizing N with
  | zero => exact UN.byte (N := N) 0 (by decide) (Nat.two_pow_pos N)
  | succ k ih =>
    have := UN.cont (N := N) 0x80 (by decide) (by omega) (ih (N := N - 7) (by omega))
    simpa [List.replicate_succ] using this

theorem u32_zero_iff (b : Bytes) :
    U32 b 0 ↔ ∃ k, k ≤ 4 ∧ b = List.replicate k 0x80 ++ [0x00] := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := zero_shape h rfl
    have := length_le (by decide) h
    simp only [List.length_append, List.length_replicate, List.length_singleton] at this
    exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact zero_enc k (by omega)

end UN

/-! ## `SN` properties -/

namespace SN

theorem bounds {N : Nat} {b : Bytes} {i : Int} (h : SN N b i) :
    -(2 : Int) ^ (N - 1) ≤ i ∧ i < 2 ^ (N - 1) := by
  induction h with
  | @pos N n _ h₂ =>
    have e : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by simp
    have := Nat.two_pow_pos (N - 1)
    rw [← e]
    omega
  | @neg N n h₁ _ h₃ =>
    have e : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by simp
    have := Nat.two_pow_pos (N - 1)
    rw [← e] at h₃ ⊢
    simp only [Int.reducePow, Nat.reducePow] at h₁ h₃ ⊢
    omega
  | @cont N n b i h₁ h₂ _ ih =>
    have hn := n.toNat_lt_size
    have e : (2 : Int) ^ (N - 1) = 2 ^ 7 * 2 ^ (N - 7 - 1) := by
      rw [← Int.pow_add]
      congr 1
      omega
    rw [e]
    simp only [Int.reducePow, Nat.reducePow, UInt8.size] at h₁ hn ih ⊢
    omega

theorem length_le {N : Nat} (hN : 0 < N) {b : Bytes} {i : Int} (h : SN N b i) :
    b.length ≤ (N + 6) / 7 := by
  induction h with
  | pos => simp only [List.length_singleton]; omega
  | neg => simp only [List.length_singleton]; omega
  | cont _ _ h₂ _ ih =>
    have := ih (by omega)
    simp only [List.length_cons]
    omega

theorem mono {N M : Nat} (hNM : N ≤ M) {b : Bytes} {i : Int} (h : SN N b i) : SN M b i := by
  induction h generalizing M with
  | pos n h₁ h₂ =>
    exact SN.pos n h₁ (Nat.lt_of_lt_of_le h₂ (Nat.pow_le_pow_right (by decide) (by omega)))
  | @neg N n h₁ h₂ h₃ =>
    have hpow : (2 : Nat) ^ (N - 1) ≤ 2 ^ (M - 1) :=
      Nat.pow_le_pow_right (by decide) (show N - 1 ≤ M - 1 by omega)
    have : (2 : Int) ^ (N - 1) ≤ 2 ^ (M - 1) := by
      have e1 : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by simp
      have e2 : ((2 ^ (M - 1) : Nat) : Int) = (2 : Int) ^ (M - 1) := by simp
      rw [← e1, ← e2]
      exact Int.ofNat_le.mpr hpow
    exact SN.neg n h₁ h₂ (by omega)
  | cont n h₁ h₂ _ ih => exact SN.cont n h₁ (by omega) (ih (by omega))

private theorem head_lt {N : Nat} {n : UInt8} {b : Bytes} {i : Int} (h : SN N (n :: b) i)
    (hn : n.toNat < 2 ^ 7) :
    b = [] ∧ i = (if n.toNat < 2 ^ 6 then (n.toNat : Int) else (n.toNat : Int) - 2 ^ 7) := by
  cases h with
  | pos _ h₁ _ => exact ⟨rfl, (ite_eq_left h₁).symm⟩
  | neg _ h₁ _ _ => exact ⟨rfl, (ite_eq_right (by omega)).symm⟩
  | cont _ h₁ _ _ => omega

theorem prefixFree (N : Nat) : PrefixFree (SN N) := by
  intro b b' r r' a a' h h' he
  induction h generalizing b' r r' a' with
  | pos n h₁ _ =>
    cases b' with
    | nil => cases h'
    | cons n' b'' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨rfl, rfl⟩ := head_lt h' (by omega)
      exact ⟨rfl, (ite_eq_left h₁).symm⟩
  | neg n h₁ h₂ _ =>
    cases b' with
    | nil => cases h'
    | cons n' b'' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨rfl, rfl⟩ := head_lt h' h₂
      exact ⟨rfl, (ite_eq_right (by omega)).symm⟩
  | cont n h₁ _ _ ih =>
    cases h' with
    | pos n' h₁' _ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      omega
    | neg n' _ h₂' _ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      omega
    | cont n' _ _ rest' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl⟩ := ih rest' he
      exact ⟨rfl, rfl⟩

theorem functional (N : Nat) : Functional (SN N) := (prefixFree N).functional

end SN

/-! ## `IN`, `FN`, `Seq`, `Vec`, `Utf8`, `Name` properties -/

theorem IN.prefixFree (N : Nat) : PrefixFree (IN N) := by
  intro _ _ _ _ _ _ h h' he
  cases h with
  | mk hs =>
    cases h' with
    | mk hs' =>
      obtain ⟨rfl, rfl⟩ := SN.prefixFree N hs hs' he
      exact ⟨rfl, rfl⟩

theorem FN.prefixFree (N : Nat) : PrefixFree (FN N) := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk hb =>
    cases ha' with
    | mk hb' =>
      obtain ⟨rfl, -⟩ := List.append_inj h (hb.trans hb'.symm)
      exact ⟨rfl, rfl⟩

theorem Seq.functional {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G)
    (hne : ∀ a, ¬ G [] a) : Functional (Seq G) := by
  intro b xs ys hs hs'
  induction hs generalizing ys with
  | nil =>
    generalize hb : ([] : Bytes) = x at hs'
    cases hs' with
    | nil => rfl
    | @cons b0 bs0 _ _ hg _ =>
      rcases b0 with _ | ⟨y, b0⟩
      · exact (hne _ hg).elim
      · simp at hb
  | @cons b bs a as hg _ ih =>
    generalize hb : b ++ bs = x at hs'
    cases hs' with
    | nil =>
      rcases b with _ | ⟨y, b⟩
      · exact (hne _ hg).elim
      · simp at hb
    | cons hg' hs' =>
      obtain ⟨rfl, rfl⟩ := h hg hg' hb
      obtain rfl := List.append_cancel_left hb
      rw [ih hs']

private theorem Seq.prefixFree_len {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G) :
    ∀ {b b' r r' : Bytes} {xs xs' : List α}, Seq G b xs → Seq G b' xs' →
      xs.length = xs'.length → b ++ r = b' ++ r' → b = b' ∧ xs = xs' := by
  intro b b' r r' xs xs' hs hs' hl he
  induction hs generalizing b' r r' xs' with
  | nil =>
    cases hs' with
    | nil => exact ⟨rfl, rfl⟩
    | cons => simp at hl
  | cons hg _ ih =>
    cases hs' with
    | nil => simp at hl
    | cons hg' hs' =>
      simp only [List.append_assoc] at he
      obtain ⟨rfl, rfl⟩ := h hg hg' he
      obtain ⟨rfl, rfl⟩ := ih hs' (by simpa using hl) (List.append_cancel_left he)
      exact ⟨rfl, rfl⟩

theorem Vec.prefixFree {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G) :
    PrefixFree (Vec G) := by
  intro _ _ _ _ _ _ h1 h2 he
  cases h1 with
  | mk hn hc =>
    cases h2 with
    | mk hn' hc' =>
      simp only [List.append_assoc] at he
      obtain ⟨rfl, hl⟩ := UN.prefixFree 32 hn hn' he
      obtain ⟨rfl, rfl⟩ := Seq.prefixFree_len h hc hc' hl (List.append_cancel_left he)
      exact ⟨rfl, rfl⟩

private def utf8Len (b : UInt8) : Nat :=
  if b.toNat < 0x80 then 0 else if b.toNat < 0xE0 then 1 else if b.toNat < 0xF0 then 2 else 3

private theorem Utf8Char.shape {c : Char} {b : Bytes} (h : Utf8Char c b) :
    ∃ b₀ t, b = b₀ :: t ∧ t.length = utf8Len b₀ := by
  cases h with
  | one b h e =>
    refine ⟨b, [], rfl, ?_⟩
    unfold utf8Len
    rw [ite_eq_left (by omega)]
    rfl
  | two b₁ b₂ lo hi h₁ h₂ e =>
    refine ⟨b₁, [b₂], rfl, ?_⟩
    unfold utf8Len
    simp only [Nat.reducePow] at e
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    rfl
  | three b₁ b₂ b₃ range h₁ h₂ h₃ e =>
    refine ⟨b₁, [b₂, b₃], rfl, ?_⟩
    unfold utf8Len
    simp only [Nat.reducePow] at e
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    rfl
  | four b₁ b₂ b₃ b₄ lo hi h₁ h₂ h₃ h₄ e =>
    refine ⟨b₁, [b₂, b₃, b₄], rfl, ?_⟩
    unfold utf8Len
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    rfl

private theorem char_eq_of_toNat_eq {c c' : Char} (h : c.toNat = c'.toNat) : c = c' :=
  Char.ext (UInt32.toNat_inj.mp h)

private theorem Utf8Char.prefixFree : PrefixFree (fun b c => Utf8Char c b) := by
  intro b b' r r' c c' h h' he
  obtain ⟨b₀, t, rfl, ht⟩ := Utf8Char.shape h
  obtain ⟨b₀', t', rfl, ht'⟩ := Utf8Char.shape h'
  simp only [List.cons_append, List.cons.injEq] at he
  obtain ⟨rfl, he⟩ := he
  obtain ⟨rfl, -⟩ := List.append_inj he (ht.trans ht'.symm)
  refine ⟨rfl, char_eq_of_toNat_eq ?_⟩
  cases h <;> cases h' <;> omega

theorem Utf8.functional : Functional (fun b (s : List Char) => Utf8 s b) :=
  fun _ _ _ h h' => Seq.functional Utf8Char.prefixFree (fun _ h => by cases h) h h'

private theorem utf8Char_encode (c : Char) : Utf8Char c (String.utf8EncodeChar c) := by
  have hv : c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) := c.valid
  have hn : c.toNat = c.val.toNat := rfl
  unfold String.utf8EncodeChar
  dsimp only
  split
  · exact Utf8Char.one _ (by omega) (by simp only [UInt8.toNat_ofNat']; omega)
  · split
    · exact Utf8Char.two _ _ (by omega) (by omega) (by simp only [UInt8.toNat_ofNat']; omega)
        ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
        (by simp only [UInt8.toNat_ofNat', Nat.reducePow]; omega)
    · split
      · exact Utf8Char.three _ _ _ (by omega) (by simp only [UInt8.toNat_ofNat']; omega)
          ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
          ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
          (by simp only [UInt8.toNat_ofNat', Nat.reducePow]; omega)
      · exact Utf8Char.four _ _ _ _ (by omega) (by omega)
          (by simp only [UInt8.toNat_ofNat']; omega)
          ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
          ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
          ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
          (by simp only [UInt8.toNat_ofNat', Nat.reducePow]; omega)

theorem Utf8.toUTF8 (s : String) : Utf8 s.toList s.toUTF8.data.toList := by
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]
  show Utf8 s.toList (s.toList.flatMap String.utf8EncodeChar)
  generalize s.toList = l
  induction l with
  | nil => exact Seq.nil
  | cons c l ih =>
    rw [List.flatMap_cons]
    exact Seq.cons (utf8Char_encode c) ih

theorem Name.prefixFree : PrefixFree Name := by
  intro _ _ _ _ _ _ h h' he
  cases h with
  | mk v u =>
    cases h' with
    | mk v' u' =>
      obtain ⟨rfl, rfl⟩ := Vec.prefixFree Byte.prefixFree v v' he
      exact ⟨rfl, String.toList_injective (Utf8.functional u u')⟩

/-! ## LEB128 encoder soundness -/

theorem encU_sound {N n : Nat} (h : n < 2 ^ N) : UN N (encU n) n := by
  rw [encU]
  split
  · next hs =>
    have e : (UInt8.ofNat n).toNat = n := u8_toNat (by omega)
    have := UN.byte (N := N) (UInt8.ofNat n) (by rw [e]; simp only [Nat.reducePow]; omega)
      (by rw [e]; exact h)
    rwa [e] at this
  · next hs =>
    have hN7 : 7 < N := by
      apply Nat.lt_of_not_le
      intro hc
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) hc
      simp only [Nat.reducePow] at this
      omega
    have e2 : 2 ^ N = 2 ^ (N - 7) * 2 ^ 7 := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hb : UN (N - 7) (encU (n / 0x80)) (n / 0x80) :=
      encU_sound (by rw [e2] at h; simp only [Nat.reducePow] at h; omega)
    have e : (UInt8.ofNat (n % 0x80 + 0x80)).toNat = n % 0x80 + 0x80 := u8_toNat (by omega)
    have := UN.cont (UInt8.ofNat (n % 0x80 + 0x80)) (by rw [e]; simp only [Nat.reducePow]; omega)
      hN7 hb
    have hv : 2 ^ 7 * (n / 0x80) + ((UInt8.ofNat (n % 0x80 + 0x80)).toNat - 2 ^ 7) = n := by
      rw [e]; simp only [Nat.reducePow]; omega
    rwa [hv] at this
termination_by n
decreasing_by omega

theorem encS_sound {N : Nat} {i : Int} (hlo : -(2 ^ (N - 1) : Int) ≤ i)
    (hhi : i < 2 ^ (N - 1)) (hN : 0 < N) : SN N (encS i) i := by
  have hP : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by simp
  rw [encS]
  split
  · next hs =>
    have h1 : (((i % 128).toNat : Nat) : Int) = i % 128 :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    have e : (UInt8.ofNat (i % 128).toNat).toNat = (i % 128).toNat := u8_toNat (by omega)
    by_cases hi : 0 ≤ i
    · have := SN.pos (N := N) (UInt8.ofNat (i % 128).toNat)
        (by rw [e]; simp only [Nat.reducePow]; omega) (by rw [e]; omega)
      have hv : (((UInt8.ofNat (i % 128).toNat).toNat : Nat) : Int) = i := by rw [e]; omega
      rwa [hv] at this
    · have := SN.neg (N := N) (UInt8.ofNat (i % 128).toNat)
        (by rw [e]; simp only [Nat.reducePow]; omega) (by rw [e]; simp only [Nat.reducePow]; omega)
        (by rw [e]; simp only [Int.reducePow]; omega)
      have hv : (((UInt8.ofNat (i % 128).toNat).toNat : Nat) : Int) - 2 ^ 7 = i := by
        rw [e]; simp only [Int.reducePow]; omega
      rwa [hv] at this
  · next hs =>
    have hN7 : 7 < N := by
      apply Nat.lt_of_not_le
      intro hc
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show N - 1 ≤ 6 by omega)
      simp only [Nat.reducePow] at this
      omega
    have e2 : (2 : Int) ^ (N - 1) = 2 ^ 7 * 2 ^ (N - 7 - 1) := by
      rw [← Int.pow_add]
      congr 1
      omega
    have hb : SN (N - 7) (encS (i / 128)) (i / 128) :=
      encS_sound (by rw [e2] at hlo; simp only [Int.reducePow] at hlo; omega)
        (by rw [e2] at hhi; simp only [Int.reducePow] at hhi; omega) (by omega)
    have h1 : (((i % 128 + 128).toNat : Nat) : Int) = i % 128 + 128 :=
      Int.toNat_of_nonneg (by omega)
    have e : (UInt8.ofNat (i % 128 + 128).toNat).toNat = (i % 128 + 128).toNat :=
      u8_toNat (by omega)
    have := SN.cont (UInt8.ofNat (i % 128 + 128).toNat)
      (by rw [e]; simp only [Nat.reducePow]; omega) hN7 hb
    have hv : (2 : Int) ^ 7 * (i / 128) +
        ((((UInt8.ofNat (i % 128 + 128).toNat).toNat : Nat) : Int) - 2 ^ 7) = i := by
      rw [e]; simp only [Int.reducePow]; omega
    rwa [hv] at this
termination_by i.natAbs
decreasing_by omega

/-- Weaken the element production of a sequence, on encodings no longer than the sequence. -/
theorem Seq.imp {α : Type} {G G' : Bytes → α → Prop} {b : Bytes}
    {xs : List α} (h : Seq G b xs) (hg : ∀ {c x}, c.length ≤ b.length → G c x → G' c x) :
    Seq G' b xs := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih =>
    refine .cons (hg (by simp only [List.length_append]; omega) hx) (ih fun hc hx' => hg ?_ hx')
    simp only [List.length_append]; omega

end Silmaril.Proofs.Parse.Binary
