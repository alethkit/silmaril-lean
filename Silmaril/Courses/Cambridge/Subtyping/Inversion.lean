module

public import Silmaril.Courses.Cambridge.Subtyping.Typing

/-! # Inversion and canonical forms for L3 with subsumption -/

public section

namespace Silmaril.Courses.Cambridge.Subtyping

open L3 (Ty Expr Label LocTypes VarTypes RecordLabels IsValue)

namespace L3Subty

theorem arr_inv {source A B : Ty} (h : L3Subty source (.arr A B)) :
    ∃ C D, source = .arr C D ∧ L3Subty A C ∧ L3Subty D B := by
  obtain ⟨C, D, shape, domain, result⟩ := Subty.function_inv h rfl
  cases source <;> cases shape
  exact ⟨_, _, rfl, domain, result⟩

theorem prod_inv {source A B : Ty} (h : L3Subty source (.prod A B)) :
    ∃ C D, source = .prod C D ∧ L3Subty C A ∧ L3Subty D B := by
  obtain ⟨C, D, shape, left, right⟩ := Subty.product_inv h rfl
  cases source <;> cases shape
  exact ⟨_, _, rfl, left, right⟩

theorem sum_inv {source A B : Ty} (h : L3Subty source (.sum A B)) :
    ∃ C D, source = .sum C D ∧ L3Subty C A ∧ L3Subty D B := by
  obtain ⟨C, D, shape, left, right⟩ := Subty.sum_inv h rfl
  cases source <;> cases shape
  exact ⟨_, _, rfl, left, right⟩

theorem record_inv {source : Ty} {labels : RecordLabels} {types : labels.Index → Ty}
    (h : L3Subty source (.record labels types)) :
    ∃ (actual : RecordLabels) (actualTypes : actual.Index → Ty),
      source = .record actual actualTypes ∧
      ∀ j : labels.Index, ∃ i : actual.Index,
        actual.label i = labels.label j ∧ L3Subty (actualTypes i) (types j) := by
  obtain ⟨fields, shape, subFields⟩ := Subty.record_inv h rfl
  cases source <;> cases shape
  refine ⟨_, _, rfl, fun j => ?_⟩
  have targetMem : (labels.label j, types j) ∈ recordFields labels types :=
    mem_recordFields.mpr ⟨j, rfl, rfl⟩
  obtain ⟨type, sourceMem, sub⟩ := subFields targetMem
  obtain ⟨i, name, rfl⟩ := mem_recordFields.mp sourceMem
  exact ⟨i, name, sub⟩

end L3Subty

/-- A value's introduction rule exposes its type before trailing subsumption. -/
inductive ValueTyping (Θ : LocTypes) (Γ : VarTypes) : Expr → Ty → Prop where
  | int (n : Int) : ValueTyping Θ Γ (.int n) .int
  | bool (b : Bool) : ValueTyping Θ Γ (.bool b) .bool
  | skip : ValueTyping Θ Γ .skip .unit
  | loc {loc : L3.Loc} {T : Ty} :
      Θ.lookup loc = some T → ValueTyping Θ Γ (.loc loc) (.ref T)
  | lam {domain codomain : Ty} {body : Expr} :
      HasType Θ (Γ.push domain) body codomain →
      ValueTyping Θ Γ (.lam domain body) (.arr domain codomain)
  | pair {left right : Expr} {A B : Ty} :
      HasType Θ Γ left A → HasType Θ Γ right B → ValueTyping Θ Γ (.pair left right) (.prod A B)
  | inl {e : Expr} {A B : Ty} :
      HasType Θ Γ e A → ValueTyping Θ Γ (.inl e (.sum A B)) (.sum A B)
  | inr {e : Expr} {A B : Ty} :
      HasType Θ Γ e B → ValueTyping Θ Γ (.inr e (.sum A B)) (.sum A B)
  | record {labels : RecordLabels} {fields : labels.Index → Expr} {types : labels.Index → Ty} :
      (∀ i, HasType Θ Γ (fields i) (types i)) →
      ValueTyping Θ Γ (.record labels fields) (.record labels types)

theorem Typing.valueTyping {Θ : LocTypes} {Γ : VarTypes} {e : Expr} {T : Ty}
    (typed : HasType Θ Γ e T) (value : IsValue e) :
    ∃ S, ValueTyping Θ Γ e S ∧ L3Subty S T := by
  induction typed <;> try (cases value; done)
  case int n => exact ⟨_, .int n, .refl _⟩
  case bool b => exact ⟨_, .bool b, .refl _⟩
  case skip => exact ⟨_, .skip, .refl _⟩
  case loc lookup => exact ⟨_, .loc lookup, .refl _⟩
  case lam typed _ => exact ⟨_, .lam typed, .refl _⟩
  case pair left right _ _ => exact ⟨_, .pair left right, .refl _⟩
  case inl typed _ => exact ⟨_, .inl typed, .refl _⟩
  case inr typed _ => exact ⟨_, .inr typed, .refl _⟩
  case record typed _ => exact ⟨_, .record typed, .refl _⟩
  case sub _ sub ih =>
    obtain ⟨_, rule, headSub⟩ := ih value
    exact ⟨_, rule, headSub.trans sub⟩

end Silmaril.Courses.Cambridge.Subtyping
