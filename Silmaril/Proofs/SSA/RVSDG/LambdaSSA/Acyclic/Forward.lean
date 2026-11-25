module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Defs

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Proofs

open LinearChain (Site)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A : τ} {L R : List τ}

theorem local_index (code : Extension Φ L R) (i : Fin code.locals.length) :
    (code.local i).index = i.val := by
  induction code with
  | empty => exact i.elim0
  | push prev b ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrArg (· + 1) (ih j)

theorem lift_index (code : Extension Φ L R) (s : Site L A) :
    (code.lift s).index = s.index + code.locals.length := by
  induction code with
  | empty => rfl
  | push prev b ih =>
    change (prev.lift s).index + 1 = s.index + (prev.locals.length + 1)
    rw [ih, Nat.add_assoc]

private theorem shift_targets (b : Block Φ L A) (X : τ) :
    (b.rename (shiftSite X)).targets = b.targets.map (· + 1) := by
  cases b <;> rfl

private theorem forward (e : Extension Φ L R) (i : Fin e.locals.length)
    (target : Nat) (mem : target ∈ (e.block i).targets) : i.val < target := by
  induction e generalizing target with
  | empty => exact i.elim0
  | push prev b ih =>
    revert mem
    refine Fin.cases (motive := fun j => target ∈ ((prev.push b).block j).targets → j.val < target)
      ?_ (fun j => ?_) i
    · intro h
      change target ∈ (b.rename (shiftSite _)).targets at h
      rw [shift_targets] at h
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp h
      exact Nat.zero_lt_succ k
    · intro h
      change target ∈ ((prev.block j).rename (shiftSite _)).targets at h
      rw [shift_targets] at h
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
      exact Nat.succ_lt_succ (ih j k hk)

theorem blockAt_forward (p : Compiled Φ L A) (i : Fin (p.rest.locals.length + 1))
    (target : Nat) (mem : target ∈ (p.blockAt i).targets) : i.val < target := by
  apply forward p.code i target
  have same (b : Block Φ p.labels (p.localTypes i)) :
      (b.rename p.site).targets = b.targets := by cases b <;> rfl
  exact (same (p.code.block i)) ▸ mem

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Proofs
