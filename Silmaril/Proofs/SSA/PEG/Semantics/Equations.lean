module

public import Silmaril.SSA.PEG.Semantics.Defs

public section

namespace Silmaril.SSA.PEG.Semantics.Proofs

open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

theorem monotonize_eq_some {α : Type x} (s : Nat → Option α) (k : Nat) (value : α) :
    monotonize s k = some value ↔ s k = some value ∧ ∀ j < k, (s j).isSome := by
  have prefixIff : (∀ j : Fin k, (s j.val).isSome) ↔ ∀ j < k, (s j).isSome :=
    ⟨fun h j lt => h ⟨j, lt⟩, fun h j => h j.val j.isLt⟩
  by_cases h : ∀ j : Fin k, (s j.val).isSome
  · rw [monotonize, ite_eq_left h]
    exact ⟨fun eq => ⟨eq, prefixIff.mp h⟩, And.left⟩
  · rw [monotonize, ite_eq_right h]
    constructor
    · intro invalid
      cases invalid
    · exact fun ⟨_, defined⟩ => (h (prefixIff.mpr defined)).elim

theorem firstTrue_eq_some (s : Nat → Option Bool) (k : Nat) :
    firstTrue s = some k ↔ monotonize s k = some true ∧
      ∀ j < k, monotonize s j ≠ some true := by
  classical
  by_cases h : ∃ j, monotonize s j = some true
  · simp only [firstTrue, dite_eq_left h, Option.some.injEq, Nat.find_eq_iff]
  · rw [firstTrue, dite_eq_right h]
    constructor
    · intro invalid
      cases invalid
    · exact fun ⟨atK, _⟩ => (h ⟨k, atK⟩).elim

theorem firstTrue_eq_none (s : Nat → Option Bool) :
    firstTrue s = none ↔ ∀ j, monotonize s j ≠ some true := by
  classical
  by_cases h : ∃ j, monotonize s j = some true
  · obtain ⟨k, hk⟩ := h
    simp only [firstTrue, dite_eq_left (show ∃ j, monotonize s j = some true from ⟨k, hk⟩),
      reduceCtorEq, false_iff]
    exact fun lacks => lacks k hk
  · simp only [firstTrue, dite_eq_right h, true_iff]
    exact fun j eq => h ⟨j, eq⟩

variable {g : Graph P params results n l} {m : Interpretation.{u,v,x} P}
variable {env : Tuple m.Value params}

theorem denote_solves (wf : WellFounded g.Demand) : g.Solves m env (g.denote m env wf) :=
  fun q => WellFounded.fix_eq wf (g.demandStep m env) q

theorem solves_unique (wf : WellFounded g.Demand) {a b : g.Valuation m}
    (ha : g.Solves m env a) (hb : g.Solves m env b) : a = b := by
  funext q
  induction q using wf.induction with
  | h q ih =>
    rw [ha q, hb q]
    apply congrArg (g.demandStep m env q)
    funext child demand
    exact ih child demand

theorem existsUnique_solves (wf : WellFounded g.Demand) :
    ∃! values, g.Solves m env values :=
  ⟨g.denote m env wf, denote_solves wf, fun _ h => solves_unique wf h (denote_solves wf)⟩

end Silmaril.SSA.PEG.Semantics.Proofs
