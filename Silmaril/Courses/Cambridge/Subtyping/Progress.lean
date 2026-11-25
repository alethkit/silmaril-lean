module

public import Silmaril.Courses.Cambridge.L3.Reduction
public import Silmaril.Courses.Cambridge.Subtyping.Inversion
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! # Cambridge L3 progress with subsumption (Exercise 36) -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Subtyping

open L3 (Op Loc Ty Expr IsValue LocTypes VarTypes Store Step)

private theorem Store.exists_fresh (s : Store) : ∃ loc : Loc, loc ∉ s := by
  refine ⟨s.keys.sup id + 1, fun present => ?_⟩
  have bound : s.keys.sup id + 1 ≤ s.keys.sup id :=
    Finset.le_sup (f := id) (Finmap.mem_keys.mpr present)
  exact Nat.not_succ_le_self _ bound

private theorem int_value {Θ : LocTypes} {Γ : VarTypes} {e : Expr}
    (typed : HasType Θ Γ e .int) (value : IsValue e) : ∃ n, e = .int n := by
  obtain ⟨_, head, h⟩ := typed.valueTyping value
  cases Subty.atom_inv h rfl
  cases head
  exact ⟨_, rfl⟩

private theorem bool_value {Θ : LocTypes} {Γ : VarTypes} {e : Expr}
    (typed : HasType Θ Γ e .bool) (value : IsValue e) : ∃ b, e = .bool b := by
  obtain ⟨_, head, h⟩ := typed.valueTyping value
  cases Subty.atom_inv h rfl
  cases head
  exact ⟨_, rfl⟩

private theorem unit_value {Θ : LocTypes} {Γ : VarTypes} {e : Expr}
    (typed : HasType Θ Γ e .unit) (value : IsValue e) : e = .skip := by
  obtain ⟨_, head, h⟩ := typed.valueTyping value
  cases Subty.atom_inv h rfl
  cases head
  rfl

private theorem ref_value {Θ : LocTypes} {Γ : VarTypes} {e : Expr} {T : Ty}
    (typed : HasType Θ Γ e (.ref T)) (value : IsValue e) :
    ∃ loc, e = .loc loc ∧ Θ.lookup loc = some T := by
  obtain ⟨_, head, h⟩ := typed.valueTyping value
  cases Subty.reference_inv h rfl
  cases head
  rename_i lookup
  exact ⟨_, rfl, lookup⟩

private theorem arithmetic_progress {Θ : LocTypes} {Γ : VarTypes} {s : Store} {left right : Expr}
    (op : Op) (hl : HasType Θ Γ left .int) (hr : HasType Θ Γ right .int)
    (pl : IsValue left ∨ ∃ next, Step ⟨left, s⟩ next)
    (pr : IsValue right ∨ ∃ next, Step ⟨right, s⟩ next) :
    ∃ next, Step ⟨.binary left op right, s⟩ next := by
  rcases pl with vl | ⟨⟨_, _⟩, step⟩
  · rcases pr with vr | ⟨⟨_, _⟩, step⟩
    · obtain ⟨a, rfl⟩ := int_value hl vl
      obtain ⟨b, rfl⟩ := int_value hr vr
      cases op
      · exact ⟨_, .add a b s⟩
      · exact ⟨_, .ge a b s⟩
    · exact ⟨_, .binaryRight vl step⟩
  · exact ⟨_, .binaryLeft step⟩

/-- An expression typed with no ambient variables can step or is already a
value, provided the current store has the same location typing. -/
theorem progress {Θ : LocTypes} {e : Expr} {T : Ty} {s : Store}
    (typed : HasType Θ .empty e T) (store : StoreTyped Θ s) :
    IsValue e ∨ ∃ next, Step ⟨e, s⟩ next := by
  generalize closed : VarTypes.empty = Γ at typed
  induction typed with
  | sub _ _ ih => exact ih closed
  | int n => exact .inl (.int n)
  | bool b => exact .inl (.bool b)
  | skip => exact .inl .skip
  | loc _ => exact .inl (.loc _)
  | lam => exact .inl (.lam _ _)
  | bvar lookup => simp [← closed, VarTypes.empty] at lookup
  | fvar lookup => simp [← closed, VarTypes.empty] at lookup
  | add hl hr ihl ihr => exact .inr (arithmetic_progress .add hl hr (ihl closed) (ihr closed))
  | ge hl hr ihl ihr => exact .inr (arithmetic_progress .ge hl hr (ihl closed) (ihr closed))
  | cond ht _ _ iht _ _ =>
      apply Or.inr
      rcases iht closed with value | ⟨⟨_, _⟩, step⟩
      · obtain ⟨b, rfl⟩ := bool_value ht value
        cases b
        · exact ⟨_, .ifFalse⟩
        · exact ⟨_, .ifTrue⟩
      · exact ⟨_, .ifStep step⟩
  | seq hl _ ihl _ =>
      apply Or.inr
      rcases ihl closed with value | ⟨⟨_, _⟩, step⟩
      · cases unit_value hl value
        exact ⟨_, .seqSkip⟩
      · exact ⟨_, .seqStep step⟩
  | loop => exact .inr ⟨_, .while⟩
  | app hf _ ihf iha =>
      apply Or.inr
      rcases ihf closed with vf | ⟨⟨_, _⟩, step⟩
      · rcases iha closed with va | ⟨⟨_, _⟩, step⟩
        · obtain ⟨_, head, sub⟩ := hf.valueTyping vf
          obtain ⟨_, _, rfl, _, _⟩ := L3Subty.arr_inv sub
          cases head
          exact ⟨_, .appFun va⟩
        · exact ⟨_, .appRight vf step⟩
      · exact ⟨_, .appLeft step⟩
  | letE _ _ ihv _ =>
      rcases ihv closed with value | ⟨⟨_, _⟩, step⟩
      · exact .inr ⟨_, .letValue value⟩
      · exact .inr ⟨_, .letStep step⟩
  | letRecFun => exact .inr ⟨_, .letRecFun⟩
  | pair _ _ ihl ihr =>
      rcases ihl closed with vl | ⟨⟨_, _⟩, step⟩
      · rcases ihr closed with vr | ⟨⟨_, _⟩, step⟩
        · exact .inl (.pair vl vr)
        · exact .inr ⟨_, .pairRight vl step⟩
      · exact .inr ⟨_, .pairLeft step⟩
  | fst typed ih =>
      apply Or.inr
      rcases ih closed with value | ⟨⟨_, _⟩, step⟩
      · obtain ⟨_, head, sub⟩ := typed.valueTyping value
        obtain ⟨_, _, rfl, _, _⟩ := L3Subty.prod_inv sub
        cases head
        cases value with
        | pair vl vr => exact ⟨_, .fstValue vl vr⟩
      · exact ⟨_, .fstStep step⟩
  | snd typed ih =>
      apply Or.inr
      rcases ih closed with value | ⟨⟨_, _⟩, step⟩
      · obtain ⟨_, head, sub⟩ := typed.valueTyping value
        obtain ⟨_, _, rfl, _, _⟩ := L3Subty.prod_inv sub
        cases head
        cases value with
        | pair vl vr => exact ⟨_, .sndValue vl vr⟩
      · exact ⟨_, .sndStep step⟩
  | inl _ ih =>
      rcases ih closed with value | ⟨⟨_, _⟩, step⟩
      · exact .inl (.inl value)
      · exact .inr ⟨_, .inl step⟩
  | inr _ ih =>
      rcases ih closed with value | ⟨⟨_, _⟩, step⟩
      · exact .inl (.inr value)
      · exact .inr ⟨_, .inr step⟩
  | matchSum typed _ _ ih _ _ =>
      apply Or.inr
      rcases ih closed with value | ⟨⟨_, _⟩, step⟩
      · obtain ⟨_, head, sub⟩ := typed.valueTyping value
        obtain ⟨_, _, rfl, _, _⟩ := L3Subty.sum_inv sub
        cases head
        · cases value with
          | inl payload => exact ⟨_, .matchLeft payload⟩
        · cases value with
          | inr payload => exact ⟨_, .matchRight payload⟩
      · exact ⟨_, .matchStep step⟩
  | @record _ labels fields _ _ ih =>
      classical
      by_cases ready : ∀ i, IsValue (fields i)
      · exact .inl (.record ready)
      · have failure : ∃ i : labels.Index, ¬ IsValue (fields i) := not_forall.mp ready
        let i := Fin.find (fun i => ¬ IsValue (fields i)) failure
        rcases ih i closed with value | ⟨⟨_, _⟩, step⟩
        · exact False.elim (Fin.find_spec failure value)
        · exact .inr ⟨_, .recordStep i (fun j earlier => not_not.mp (Fin.find_min failure earlier)) step⟩
  | project i typed ih =>
      apply Or.inr
      rcases ih closed with value | ⟨⟨_, _⟩, step⟩
      · obtain ⟨_, head, sub⟩ := typed.valueTyping value
        obtain ⟨_, _, rfl, fields⟩ := L3Subty.record_inv sub
        obtain ⟨j, name, _⟩ := fields i
        cases head
        cases value with
        | record ready =>
          rw [← name]
          exact ⟨_, .projectValue j ready⟩
      · exact ⟨_, .projectStep step⟩
  | ref _ ih =>
      apply Or.inr
      rcases ih closed with value | ⟨⟨_, _⟩, step⟩
      · obtain ⟨loc, fresh⟩ := Store.exists_fresh s
        exact ⟨_, .refValue (loc := loc) ⟨_, value⟩ fresh⟩
      · exact ⟨_, .refStep step⟩
  | assign hl _ ihl ihr =>
      apply Or.inr
      rcases ihl closed with vl | ⟨⟨_, _⟩, step⟩
      · obtain ⟨loc, rfl, lookup⟩ := ref_value hl vl
        rcases ihr closed with vr | ⟨⟨_, _⟩, step⟩
        · exact ⟨_, .assignValue ⟨_, vr⟩ ((store.domain loc).mp (Finmap.mem_of_lookup_eq_some lookup))⟩
        · exact ⟨_, .assignRight step⟩
      · exact ⟨_, .assignLeft step⟩
  | deref typed ih =>
      apply Or.inr
      rcases ih closed with value | ⟨⟨_, _⟩, step⟩
      · obtain ⟨loc, rfl, lookup⟩ := ref_value typed value
        obtain ⟨v, present⟩ := Finmap.mem_iff.mp ((store.domain loc).mp (Finmap.mem_of_lookup_eq_some lookup))
        exact ⟨_, .derefValue (value := v) present⟩
      · exact ⟨_, .derefStep step⟩

end Silmaril.Courses.Cambridge.Subtyping
