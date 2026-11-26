module

public import Silmaril.Semantics.Relational.UB.All

/-! Checked examples using only the public UB interface. -/

namespace Silmaril.Relational.UB.Examples

example : CompleteLattice (Explicit Nat Bool) := inferInstance

noncomputable example : CompleteLattice (Catastrophic Nat) := inferInstance

noncomputable example : CompleteLattice (WithBot (NonemptyCatastrophic Nat)) :=
  WithoutBottom.completionLattice

private def left : Explicit Bool Bool := ({false}, {false})
private def right : Explicit Bool Bool := ({true}, {true})

-- Collapse forgets both the ordinary result and the reason.
example : left.collapse = right.collapse ∧ ¬ left ≤ right := by
  refine ⟨(Explicit.collapse_eq_collapse_iff left right).mpr (Or.inr ⟨?_, ?_⟩), ?_⟩
  · exact (Set.singleton_nonempty false).ne_empty
  · exact (Set.singleton_nonempty true).ne_empty
  · intro refine
    have seen : false ∈ ({true} : Set Bool) := refine.2 (Set.mem_singleton false)
    exact Bool.noConfusion (Set.mem_singleton_iff.mp seen)

example : (⊤ : Catastrophic Bool).forget = (Catastrophic.defined (Set.univ : Set Bool)).forget :=
  rfl

example : ¬ (⊤ : Catastrophic Bool) ≤ Catastrophic.defined Set.univ :=
  WithTop.not_top_le_coe _

private def falseOnly : NonemptyCatastrophic Bool :=
  ⟨Catastrophic.defined {false}, (Catastrophic.defined_ne_bot_iff _).mpr (Set.singleton_nonempty _)⟩

private def trueOnly : NonemptyCatastrophic Bool :=
  ⟨Catastrophic.defined {true}, (Catastrophic.defined_ne_bot_iff _).mpr (Set.singleton_nonempty _)⟩

example : ¬ ∃ bottom : NonemptyCatastrophic Bool, ∀ other, bottom ≤ other := by
  rintro ⟨bottom, least⟩
  exact Catastrophic.no_common_lower_bound (by decide) falseOnly trueOnly rfl rfl
    ⟨bottom, least falseOnly, least trueOnly⟩

example : (WithoutBottom.bottomCompletion (⊥ : WithBot (NonemptyCatastrophic Bool))) = ⊥ :=
  WithoutBottom.bottomCompletion_apply _

private def embed : Unit ↪ Bool := ⟨fun _ => false, fun _ _ _ => Subsingleton.elim _ _⟩

private def count : ExplicitQuery Nat Unit (Except String Nat) Unit :=
  ExplicitQuery.ofQueryRel (QueryRel.ofTotal fun n _ => .ok n)

example : ((count.extendUB embed ()).forget.restrict embed) 7 () (.ok 7) := by
  simp only [ExplicitQuery.forget_extendUB, QueryRel.restrict_extend, ExplicitQuery.forget_ofQueryRel,
    count]
  rfl

example : (count.extendUB embed ()).collapse 7 true = ⊤ := by
  rw [ExplicitQuery.collapse_extendUB]
  apply CatastrophicQuery.extendUB_apply_outside
  rintro ⟨query, eq⟩
  change false = true at eq
  cases eq

-- A reported query failure is an ordinary outcome of a safe model.
example : (Explicit.defined (Reason := Unit) ({Except.error "bad column"} : Set (Except String Nat))).Safe :=
  Explicit.safe_defined _

end Silmaril.Relational.UB.Examples
