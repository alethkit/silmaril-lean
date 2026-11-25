module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.JumpResolution.Defs

public section

universe w

namespace Silmaril.Calco2019.Proofs.IterationJumpResolution

open IterationTheory

variable {σ : Signature.{w}} {I E : Arity} {g : Wiring σ I E}

private theorem jump_connect {S T : Type} (x : Instruction σ E S) (f : S → T) :
    (x.connect f (fun e => .head (.exit e))).IsJump ↔ x.IsJump := by
  cases x with
  | jump _ => rfl
  | head h => cases h <;> rfl

theorem contract_decreases (s : g.states) (t : g.without s) (row : g.row s = .jump t.val) :
    (g.contract s t).jumpCount < g.jumpCount := by
  classical
  let A := {i : (g.contract s t).states // ((g.contract s t).row i).IsJump}
  let B := {i : g.states // (g.row i).IsJump}
  have : Fintype A := Fintype.ofFinite _
  have : Fintype B := Fintype.ofFinite _
  let includeState (i : A) : B :=
    ⟨i.val.val, (jump_connect (g.row i.val.val) (g.redirect s t)).mp i.property⟩
  have injective : Function.Injective includeState :=
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun b : B => b.val) h))
  have omitted : (⟨s, by rw [row]; trivial⟩ : B) ∉ Set.range includeState := by
    rintro ⟨i, hi⟩
    exact i.val.property (congrArg Subtype.val hi)
  change Nat.card A < Nat.card B
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_of_notMem includeState injective omitted

theorem cut_decreases (s : g.states) (row : g.row s = .jump s) :
    (g.cut s).jumpCount < g.jumpCount := by
  classical
  let A := {i : (g.cut s).states // ((g.cut s).row i).IsJump}
  let B := {i : g.states // (g.row i).IsJump}
  have : Fintype A := Fintype.ofFinite _
  have : Fintype B := Fintype.ofFinite _
  have kept (i : A) : i.val ≠ s ∧ (g.row i.val).IsJump := by
    have hi := i.property
    change (if i.val = s then Instruction.head .bottom else g.row i.val).IsJump at hi
    split at hi
    · exact False.elim hi
    · exact ⟨by assumption, hi⟩
  let includeState (i : A) : B := ⟨i.val, (kept i).2⟩
  have injective : Function.Injective includeState :=
    fun _ _ h => Subtype.ext (congrArg (fun b : B => b.val) h)
  have omitted : (⟨s, by rw [row]; trivial⟩ : B) ∉ Set.range includeState := by
    rintro ⟨i, hi⟩
    exact (kept i).1 (congrArg Subtype.val hi)
  change Nat.card A < Nat.card B
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_of_notMem includeState injective omitted

theorem exists_normalization (g : Wiring σ I E) : ∃ r, g.Normalizes r := by
  classical
  induction h : g.jumpCount using Nat.strong_induction_on generalizing g with
  | ind n ih =>
    by_cases any : ∃ (s t : g.states), g.row s = .jump t
    · obtain ⟨s, t, row⟩ := any
      by_cases ht : t = s
      · subst t
        obtain ⟨r, norm⟩ := ih _ ((cut_decreases s row).trans_eq h) (g.cut s) rfl
        exact ⟨r, .cut s row norm⟩
      · let target : g.without s := ⟨t, ht⟩
        obtain ⟨r, norm⟩ := ih _ ((contract_decreases s target row).trans_eq h)
          (g.contract s target) rfl
        exact ⟨r, .contract s target row norm⟩
    · let r : Wiring.Ranked σ I E := ⟨g.states, g.entry, fun s => match g.row s with
        | .head h => h
        | .jump _ => .bottom⟩
      refine ⟨r, ?_⟩
      have same : r.toWiring = g := by
        cases g with
        | mk states entry row =>
          change Wiring.mk states entry _ = Wiring.mk states entry row
          congr 1
          funext s
          cases e : row s with
          | head _ => simp [r, e]
          | jump t => exact (any ⟨s, t, e⟩).elim
      exact same ▸ Wiring.Normalizes.done r

end Silmaril.Calco2019.Proofs.IterationJumpResolution
