module

public import Silmaril.Semantics.Calco2019.Examples.Printing.FiniteWriter.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.FiniteWriter.Proofs

open Silmaril.Elgot
open SetModels (NonemptyPowerset)

variable {A X Y : Type u}

theorem mem_outcomes (p : Model A X) (word : List A) (x : X) :
    (word, x) ∈ outcomes p ↔ (x, FreeMonoid.ofList word) ∈ p.run.1.run := by
  change (word, x) ∈ wordResult '' p.run.1.run ↔ _
  constructor
  · rintro ⟨q, hq, eq⟩
    have same := wordResult.injective (eq.trans (wordResult.apply_symm_apply (word, x)).symm)
    change q = (x, FreeMonoid.ofList word) at same
    exact same ▸ hq
  · intro h
    exact ⟨_, h, wordResult.apply_symm_apply (word, x)⟩

theorem outcomes_pure (x : X) : outcomes (pure x : Model A X) = {([], x)} := by
  ext ⟨word, y⟩
  rw [mem_outcomes]
  change (y, FreeMonoid.ofList word) ∈ (pure (x, (1 : FreeMonoid A)) : SetM _).run ↔ _
  rw [Nondet.mem_pure_iff, Set.mem_singleton_iff, Prod.mk.injEq, Prod.mk.injEq, and_comm]
  exact and_congr_left' ⟨fun h => congrArg FreeMonoid.toList h, fun h => h ▸ rfl⟩

private theorem mem_map {U V : Type u} (f : U → V) (p : NonemptyPowerset U) (v : V) :
    v ∈ (f <$> p).1.run ↔ ∃ u ∈ p.1.run, f u = v := by
  rw [← bind_pure_comp]
  simp only [NonemptyPowerset.val_bind, NonemptyPowerset.val_pure,
    Nondet.mem_bind_iff, Nondet.mem_pure_iff, eq_comm (a := v)]

theorem mem_outcomes_bind (p : Model A X) (k : X → Model A Y) (word : List A) (y : Y) :
    (word, y) ∈ outcomes (p >>= k) ↔
      ∃ prefixWord x suffixWord,
        (prefixWord, x) ∈ outcomes p ∧ (suffixWord, y) ∈ outcomes (k x) ∧
          prefixWord ++ suffixWord = word := by
  rw [mem_outcomes]
  change (y, FreeMonoid.ofList word) ∈ (p.run >>= fun (x, w) =>
    (fun (z, v) => (z, w * v)) <$> (k x).run).1.run ↔ _
  simp only [NonemptyPowerset.val_bind, Nondet.mem_bind_iff]
  constructor
  · rintro ⟨⟨x, w⟩, hp, hy⟩
    obtain ⟨⟨z, v⟩, hk, eq⟩ := (mem_map _ _ _).1 hy
    have pairs := Prod.mk.inj eq
    have result : z = y := pairs.1
    subst z
    exact ⟨w.toList, x, v.toList, (mem_outcomes _ _ _).2 hp, (mem_outcomes _ _ _).2 hk,
      congrArg FreeMonoid.toList pairs.2⟩
  · rintro ⟨w, x, v, hp, hk, rfl⟩
    refine ⟨(x, FreeMonoid.ofList w), (mem_outcomes _ _ _).1 hp, (mem_map _ _ _).2 ?_⟩
    exact ⟨(y, FreeMonoid.ofList v), (mem_outcomes _ _ _).1 hk, rfl⟩

end Silmaril.Calco2019.Examples.Printing.FiniteWriter.Proofs
