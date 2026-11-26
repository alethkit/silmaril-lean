module

public import Silmaril.Semantics.Dataflow.Flat.Defs
public import Mathlib.Order.Monotone.Basic

public section

namespace Silmaril.Semantics.Dataflow.Flat.Proofs

variable {α β γ : Type*}

theorem rank_strict : StrictMono (@rank α) := by
  intro a b strict
  have le := strict.le
  have ne := strict.ne
  change Flat.le a b at le
  cases a <;> cases b <;> simp_all [Flat.le, rank]

theorem covers_mono {a b : Flat α} {v : α} (h : a ≤ b) (cover : a.Covers v) : b.Covers v := by
  change Flat.le a b at h
  cases a <;> cases b <;> simp_all [Flat.le, Covers]

theorem le_join_left [DecidableEq α] (a b : Flat α) : a ≤ join a b := by
  change Flat.le a (join a b)
  cases a <;> cases b <;> simp [Flat.le, join]
  rename_i a b
  by_cases same : a = b <;> simp [same]

theorem le_join_right [DecidableEq α] (a b : Flat α) : b ≤ join a b := by
  change Flat.le b (join a b)
  cases a <;> cases b <;> simp [Flat.le, join]
  rename_i a b
  by_cases same : a = b <;> simp [same]

theorem join_le [DecidableEq α] {a b c : Flat α} (h₁ : a ≤ c) (h₂ : b ≤ c) : join a b ≤ c := by
  change Flat.le a c at h₁
  change Flat.le b c at h₂
  change Flat.le (join a b) c
  cases a <;> cases b <;> cases c <;> simp_all [Flat.le, join]
  split_ifs <;> simp_all

theorem map_mono (f : α → β) : Monotone (map f) := by
  intro a b le
  change Flat.le a b at le
  change Flat.le (map f a) (map f b)
  cases a <;> cases b <;> simp_all [Flat.le, map]

theorem map₂_mono (f : α → β → γ) {a a' : Flat α} {b b' : Flat β} (ha : a ≤ a') (hb : b ≤ b') :
    map₂ f a b ≤ map₂ f a' b' := by
  change Flat.le a a' at ha
  change Flat.le b b' at hb
  change Flat.le (map₂ f a b) (map₂ f a' b')
  cases a <;> cases a' <;> cases b <;> cases b' <;> simp_all [Flat.le, map₂]

theorem map_covers (f : α → β) {a : Flat α} {x : α} (h : a.Covers x) :
    (map f a).Covers (f x) := by
  cases a <;> simp_all [map, Covers]

theorem map₂_covers (f : α → β → γ) {a : Flat α} {b : Flat β} {x : α} {y : β}
    (ha : a.Covers x) (hb : b.Covers y) : (map₂ f a b).Covers (f x y) := by
  cases a <;> cases b <;> simp_all [map₂, Covers]

end Silmaril.Semantics.Dataflow.Flat.Proofs
