module

public import Silmaril.Semantics.Dataflow.Flat.Defs
public import Silmaril.Semantics.Dataflow.FiniteHeight.Defs
import Silmaril.Proofs.Semantics.Dataflow.Flat.Order

/-! Finite-height and concretization laws for flat facts. -/

@[expose] public section

namespace Silmaril.Semantics.Dataflow.Flat

variable {α β γ : Type*}

theorem rank_strict : StrictMono (@rank α) := Proofs.rank_strict

def height (α : Type*) : FiniteHeight.HeightBound (Flat α) where
  rank := rank
  bound := 2
  rank_strict := rank_strict
  rank_le a := by cases a <;> simp [rank]

theorem covers_mono {a b : Flat α} {v : α} (h : a ≤ b) (cover : a.Covers v) : b.Covers v :=
  Proofs.covers_mono h cover

theorem le_join_left [DecidableEq α] (a b : Flat α) : a ≤ join a b :=
  Proofs.le_join_left a b

theorem le_join_right [DecidableEq α] (a b : Flat α) : b ≤ join a b :=
  Proofs.le_join_right a b

theorem join_le [DecidableEq α] {a b c : Flat α} (h₁ : a ≤ c) (h₂ : b ≤ c) : join a b ≤ c :=
  Proofs.join_le h₁ h₂

instance [DecidableEq α] : SemilatticeSup (Flat α) where
  sup := join
  le_sup_left := le_join_left
  le_sup_right := le_join_right
  sup_le := fun _ _ _ => join_le

theorem map_mono (f : α → β) : Monotone (map f) := Proofs.map_mono f

theorem map₂_mono (f : α → β → γ) {a a' : Flat α} {b b' : Flat β} (ha : a ≤ a') (hb : b ≤ b') :
    map₂ f a b ≤ map₂ f a' b' :=
  Proofs.map₂_mono f ha hb

theorem map_covers (f : α → β) {a : Flat α} {x : α} (h : a.Covers x) : (map f a).Covers (f x) :=
  Proofs.map_covers f h

theorem map₂_covers (f : α → β → γ) {a : Flat α} {b : Flat β} {x : α} {y : β}
    (ha : a.Covers x) (hb : b.Covers y) : (map₂ f a b).Covers (f x y) :=
  Proofs.map₂_covers f ha hb

end Silmaril.Semantics.Dataflow.Flat
