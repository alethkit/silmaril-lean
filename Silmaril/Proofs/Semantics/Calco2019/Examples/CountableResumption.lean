module

public import Mathlib.Data.QPF.Univariate.Basic
public import Silmaril.Semantics.Calco2019.Examples.CountableResumption.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.CountableResumption.Proofs

open Silmaril.Elgot

theorem choice_ext {X : Type u} {p q : Choice X} (h : p.outcomes = q.outcomes) : p = q :=
  Subtype.ext (Subtype.ext h)

theorem choice_mem_map {X Y : Type u} (f : X → Y) (p : Choice X) (y : Y) :
    y ∈ (f <$> p).outcomes ↔ y ∈ f '' p.outcomes := by
  change y ∈ ((p >>= fun x => pure (f x)).1.1).run ↔ _
  simp only [Choice.val_bind, Choice.val_pure, SetModels.NonemptyPowerset.val_bind,
    SetModels.NonemptyPowerset.val_pure, Nondet.mem_bind_iff, Set.mem_image, Choice.outcomes]
  exact exists_congr fun _ => and_congr_right' (Nondet.mem_pure_iff.trans eq_comm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem choice_lawful : LawfulMonad (Choice.{u}) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := fun p => Subtype.ext (bind_pure p.1))
  (pure_bind := fun x f => Subtype.ext (pure_bind x (fun x => (f x).1)))
  (bind_assoc := fun p f g => Subtype.ext (bind_assoc p.1 (fun x => (f x).1) (fun y => (g y).1)))

open Enumeration

variable {A X : Type u} (B : A → Type u)

theorem abs_repr {Z : Type u} (p : Layer B X Z) : abs B (repr B p) = p := by
  apply choice_ext
  change Set.range (fun i => pack B (tag B (enumerate B p i)) (reply B (enumerate B p i))) =
    p.outcomes
  simp only [pack_reply]
  exact (enumerate_range B p).symm

theorem abs_map {Z W : Type u} (f : Z → W) (p : polynomial B X Z) :
    abs B ((polynomial B X).map f p) = stepMap f <$> (abs B p : Choice (Step B X Z)) := by
  apply choice_ext
  ext t
  rw [choice_mem_map]
  change t ∈ Set.range (fun i => pack B (p.1 i) (f ∘ fun r => p.2 ⟨i, r⟩)) ↔
    t ∈ stepMap f '' Set.range (fun i => pack B (p.1 i) fun r => p.2 ⟨i, r⟩)
  simp only [pack_map, Set.range_comp']

end Silmaril.Calco2019.Examples.CountableResumption.Proofs
