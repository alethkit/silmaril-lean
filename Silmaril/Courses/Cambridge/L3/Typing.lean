module

public import Silmaril.Courses.Cambridge.L3.Store

/-! # Cambridge L3 expression and store typing

Sewell §5.5, pp. 80–82, and Definition 22, p. 75.
A location environment records the contents type `T` of a location whose
expression type is `T ref`. The variable environment is independent.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

abbrev LocTypes := Finmap (fun _ : Loc => Ty)

structure VarTypes where
  free : Finmap (fun _ : Var => Ty)
  bound : List Ty

def VarTypes.empty : VarTypes := ⟨∅, []⟩

def VarTypes.push (Γ : VarTypes) (T : Ty) : VarTypes :=
  { Γ with bound := T :: Γ.bound }

inductive HasType (Θ : LocTypes) : VarTypes → Expr → Ty → Prop where
  | int {Γ : VarTypes} (n : Int) : HasType Θ Γ (.int n) .int
  | bool {Γ : VarTypes} (b : Bool) : HasType Θ Γ (.bool b) .bool
  | add {Γ : VarTypes} {left right : Expr} :
      HasType Θ Γ left .int → HasType Θ Γ right .int →
      HasType Θ Γ (.binary left .add right) .int
  | ge {Γ : VarTypes} {left right : Expr} :
      HasType Θ Γ left .int → HasType Θ Γ right .int →
      HasType Θ Γ (.binary left .ge right) .bool
  | cond {Γ : VarTypes} {test yes no : Expr} {T : Ty} :
      HasType Θ Γ test .bool → HasType Θ Γ yes T → HasType Θ Γ no T →
      HasType Θ Γ (.cond test yes no) T
  | skip {Γ : VarTypes} : HasType Θ Γ .skip .unit
  | seq {Γ : VarTypes} {left right : Expr} {T : Ty} :
      HasType Θ Γ left .unit → HasType Θ Γ right T → HasType Θ Γ (.seq left right) T
  | loop {Γ : VarTypes} {test body : Expr} :
      HasType Θ Γ test .bool → HasType Θ Γ body .unit → HasType Θ Γ (.loop test body) .unit
  | bvar {Γ : VarTypes} {index : Nat} {T : Ty} :
      Γ.bound[index]? = some T → HasType Θ Γ (.bvar index) T
  | fvar {Γ : VarTypes} {name : Var} {T : Ty} :
      Γ.free.lookup name = some T → HasType Θ Γ (.fvar name) T
  | lam {Γ : VarTypes} {domain codomain : Ty} {body : Expr} :
      HasType Θ (Γ.push domain) body codomain → HasType Θ Γ (.lam domain body) (.arr domain codomain)
  | app {Γ : VarTypes} {fn arg : Expr} {domain codomain : Ty} :
      HasType Θ Γ fn (.arr domain codomain) → HasType Θ Γ arg domain → HasType Θ Γ (.app fn arg) codomain
  | letE {Γ : VarTypes} {A B : Ty} {value body : Expr} :
      HasType Θ Γ value A → HasType Θ (Γ.push A) body B → HasType Θ Γ (.letE A value body) B
  | letRecFun {Γ : VarTypes} {domain codomain T : Ty} {functionBody body : Expr} :
      HasType Θ ((Γ.push (.arr domain codomain)).push domain) functionBody codomain →
      HasType Θ (Γ.push (.arr domain codomain)) body T →
      HasType Θ Γ (.letRecFun domain codomain functionBody body) T
  | pair {Γ : VarTypes} {left right : Expr} {A B : Ty} :
      HasType Θ Γ left A → HasType Θ Γ right B → HasType Θ Γ (.pair left right) (.prod A B)
  | fst {Γ : VarTypes} {e : Expr} {A B : Ty} :
      HasType Θ Γ e (.prod A B) → HasType Θ Γ (.fst e) A
  | snd {Γ : VarTypes} {e : Expr} {A B : Ty} :
      HasType Θ Γ e (.prod A B) → HasType Θ Γ (.snd e) B
  | inl {Γ : VarTypes} {e : Expr} {A B : Ty} :
      HasType Θ Γ e A → HasType Θ Γ (.inl e (.sum A B)) (.sum A B)
  | inr {Γ : VarTypes} {e : Expr} {A B : Ty} :
      HasType Θ Γ e B → HasType Θ Γ (.inr e (.sum A B)) (.sum A B)
  | matchSum {Γ : VarTypes} {e left right : Expr} {A B T : Ty} :
      HasType Θ Γ e (.sum A B) → HasType Θ (Γ.push A) left T → HasType Θ (Γ.push B) right T →
      HasType Θ Γ (.matchSum e A left B right) T
  | record {Γ : VarTypes} {labels : RecordLabels} {fields : labels.Index → Expr}
      {types : labels.Index → Ty} :
      (∀ i, HasType Θ Γ (fields i) (types i)) → HasType Θ Γ (.record labels fields) (.record labels types)
  | project {Γ : VarTypes} {e : Expr} {labels : RecordLabels} {types : labels.Index → Ty}
      (i : labels.Index) :
      HasType Θ Γ e (.record labels types) → HasType Θ Γ (.project e (labels.label i)) (types i)
  | ref {Γ : VarTypes} {e : Expr} {T : Ty} :
      HasType Θ Γ e T → HasType Θ Γ (.ref e) (.ref T)
  | assign {Γ : VarTypes} {lhs rhs : Expr} {T : Ty} :
      HasType Θ Γ lhs (.ref T) → HasType Θ Γ rhs T → HasType Θ Γ (.assign lhs rhs) .unit
  | deref {Γ : VarTypes} {e : Expr} {T : Ty} :
      HasType Θ Γ e (.ref T) → HasType Θ Γ (.deref e) T
  | loc {Γ : VarTypes} {loc : Loc} {T : Ty} :
      Θ.lookup loc = some T → HasType Θ Γ (.loc loc) (.ref T)

/-- Existing locations retain their contents types when the store grows. -/
def LocTypes.Extends (Θ Θ' : LocTypes) : Prop :=
  ∀ {loc T}, Θ.lookup loc = some T → Θ'.lookup loc = some T

theorem LocTypes.Extends.refl (Θ : LocTypes) : Θ.Extends Θ := fun h => h

theorem LocTypes.Extends.trans {Θ₁ Θ₂ Θ₃ : LocTypes}
    (h₁₂ : Θ₁.Extends Θ₂) (h₂₃ : Θ₂.Extends Θ₃) : Θ₁.Extends Θ₃ :=
  fun h => h₂₃ (h₁₂ h)

/-- Definition 22 with closed stored values. Locations inside a stored value
are typed in the same location environment as the store itself. -/
structure StoreTyped (Θ : LocTypes) (s : Store) : Prop where
  domain : ∀ loc, loc ∈ Θ ↔ loc ∈ s
  contents : ∀ {loc T value}, Θ.lookup loc = some T → s.lookup loc = some value →
    HasType Θ .empty value.val T

theorem StoreTyped.empty : StoreTyped ∅ ∅ where
  domain _ := iff_of_false Finmap.notMem_empty Finmap.notMem_empty
  contents := by
    intro loc T value lookup _
    rw [Finmap.lookup_empty] at lookup
    contradiction

end Silmaril.Courses.Cambridge.L3
