module

public import Silmaril.Courses.Cambridge.L3.Typing
public import Silmaril.Courses.Cambridge.Subtyping.Metatheory
import Init.Data.List.OfFn

/-! # L3 typing with subsumption (Cambridge Semantics, slide 205)

The syntax, variable and location environments, and finite stores are L3's.
The typing rules in §5.5 use the extended judgment in their premises,
so subsumption can occur anywhere in a derivation.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Subtyping

open L3 (Ty Expr Label Var Loc VarTypes LocTypes Store RecordLabels)

/-- Read the ordered, distinct fields of an L3 record as a list. -/
def recordFields (labels : RecordLabels) (types : labels.Index → Ty) : List (Label × Ty) :=
  List.ofFn fun i => (labels.label i, types i)

theorem mem_recordFields {labels : RecordLabels} {types : labels.Index → Ty}
    {label : Label} {type : Ty} :
    (label, type) ∈ recordFields labels types ↔ ∃ i, labels.label i = label ∧ types i = type := by
  simp only [recordFields, List.mem_ofFn, Prod.mk.injEq]

/-- An outer view of L3's own types. -/
def l3Types : TypeView Ty Label where
  form
    | .int | .bool | .unit => .atom
    | .arr domain codomain => .function domain codomain
    | .prod left right => .product left right
    | .sum left right => .sum left right
    | .ref contents => .reference contents
    | .record labels types => .record (recordFields labels types)
  distinctLabels := by
    intro type fields form
    cases type <;> cases form
    next labels _ =>
      rw [recordFields, List.map_ofFn]
      change (List.ofFn fun i : labels.Index => labels.names[i.val]).Nodup
      rw [List.ofFn_getElem]
      exact labels.distinct

abbrev L3Subty := Subty l3Types

/-- L3's expression typing rules and subsumption. The subtype premise is
parameterized so Exercise 33 can also be stated for the proposed reference rules. -/
inductive Typing (subtype : Ty → Ty → Prop) (Θ : LocTypes) : VarTypes → Expr → Ty → Prop where
  | int {Γ : VarTypes} (n : Int) : Typing subtype Θ Γ (.int n) .int
  | bool {Γ : VarTypes} (b : Bool) : Typing subtype Θ Γ (.bool b) .bool
  | add {Γ : VarTypes} {left right : Expr} :
      Typing subtype Θ Γ left .int → Typing subtype Θ Γ right .int →
      Typing subtype Θ Γ (.binary left .add right) .int
  | ge {Γ : VarTypes} {left right : Expr} :
      Typing subtype Θ Γ left .int → Typing subtype Θ Γ right .int →
      Typing subtype Θ Γ (.binary left .ge right) .bool
  | cond {Γ : VarTypes} {test yes no : Expr} {T : Ty} :
      Typing subtype Θ Γ test .bool → Typing subtype Θ Γ yes T → Typing subtype Θ Γ no T →
      Typing subtype Θ Γ (.cond test yes no) T
  | skip {Γ : VarTypes} : Typing subtype Θ Γ .skip .unit
  | seq {Γ : VarTypes} {left right : Expr} {T : Ty} :
      Typing subtype Θ Γ left .unit → Typing subtype Θ Γ right T → Typing subtype Θ Γ (.seq left right) T
  | loop {Γ : VarTypes} {test body : Expr} :
      Typing subtype Θ Γ test .bool → Typing subtype Θ Γ body .unit → Typing subtype Θ Γ (.loop test body) .unit
  | bvar {Γ : VarTypes} {index : Nat} {T : Ty} :
      Γ.bound[index]? = some T → Typing subtype Θ Γ (.bvar index) T
  | fvar {Γ : VarTypes} {name : Var} {T : Ty} :
      Γ.free.lookup name = some T → Typing subtype Θ Γ (.fvar name) T
  | lam {Γ : VarTypes} {domain codomain : Ty} {body : Expr} :
      Typing subtype Θ (Γ.push domain) body codomain → Typing subtype Θ Γ (.lam domain body) (.arr domain codomain)
  | app {Γ : VarTypes} {fn arg : Expr} {domain codomain : Ty} :
      Typing subtype Θ Γ fn (.arr domain codomain) → Typing subtype Θ Γ arg domain → Typing subtype Θ Γ (.app fn arg) codomain
  | letE {Γ : VarTypes} {A B : Ty} {value body : Expr} :
      Typing subtype Θ Γ value A → Typing subtype Θ (Γ.push A) body B → Typing subtype Θ Γ (.letE A value body) B
  | letRecFun {Γ : VarTypes} {domain codomain T : Ty} {functionBody body : Expr} :
      Typing subtype Θ ((Γ.push (.arr domain codomain)).push domain) functionBody codomain →
      Typing subtype Θ (Γ.push (.arr domain codomain)) body T →
      Typing subtype Θ Γ (.letRecFun domain codomain functionBody body) T
  | pair {Γ : VarTypes} {left right : Expr} {A B : Ty} :
      Typing subtype Θ Γ left A → Typing subtype Θ Γ right B → Typing subtype Θ Γ (.pair left right) (.prod A B)
  | fst {Γ : VarTypes} {e : Expr} {A B : Ty} :
      Typing subtype Θ Γ e (.prod A B) → Typing subtype Θ Γ (.fst e) A
  | snd {Γ : VarTypes} {e : Expr} {A B : Ty} :
      Typing subtype Θ Γ e (.prod A B) → Typing subtype Θ Γ (.snd e) B
  | inl {Γ : VarTypes} {e : Expr} {A B : Ty} :
      Typing subtype Θ Γ e A → Typing subtype Θ Γ (.inl e (.sum A B)) (.sum A B)
  | inr {Γ : VarTypes} {e : Expr} {A B : Ty} :
      Typing subtype Θ Γ e B → Typing subtype Θ Γ (.inr e (.sum A B)) (.sum A B)
  | matchSum {Γ : VarTypes} {e left right : Expr} {A B T : Ty} :
      Typing subtype Θ Γ e (.sum A B) → Typing subtype Θ (Γ.push A) left T → Typing subtype Θ (Γ.push B) right T →
      Typing subtype Θ Γ (.matchSum e A left B right) T
  | record {Γ : VarTypes} {labels : RecordLabels} {fields : labels.Index → Expr}
      {types : labels.Index → Ty} :
      (∀ i, Typing subtype Θ Γ (fields i) (types i)) → Typing subtype Θ Γ (.record labels fields) (.record labels types)
  | project {Γ : VarTypes} {e : Expr} {labels : RecordLabels} {types : labels.Index → Ty}
      (i : labels.Index) :
      Typing subtype Θ Γ e (.record labels types) → Typing subtype Θ Γ (.project e (labels.label i)) (types i)
  | ref {Γ : VarTypes} {e : Expr} {T : Ty} :
      Typing subtype Θ Γ e T → Typing subtype Θ Γ (.ref e) (.ref T)
  | assign {Γ : VarTypes} {lhs rhs : Expr} {T : Ty} :
      Typing subtype Θ Γ lhs (.ref T) → Typing subtype Θ Γ rhs T → Typing subtype Θ Γ (.assign lhs rhs) .unit
  | deref {Γ : VarTypes} {e : Expr} {T : Ty} :
      Typing subtype Θ Γ e (.ref T) → Typing subtype Θ Γ (.deref e) T
  | loc {Γ : VarTypes} {loc : Loc} {T : Ty} :
      Θ.lookup loc = some T → Typing subtype Θ Γ (.loc loc) (.ref T)

  | sub {Γ : VarTypes} {e : Expr} {source target : Ty} :
      Typing subtype Θ Γ e source → subtype source target → Typing subtype Θ Γ e target

abbrev HasType := Typing L3Subty

/-- Every core L3 derivation is also a derivation in the extended system. -/
theorem HasType.ofL3 {Θ : LocTypes} {Γ : VarTypes} {e : Expr} {T : Ty}
    (typed : L3.HasType Θ Γ e T) : HasType Θ Γ e T := by
  induction typed with
  | loc lookup => exact .loc lookup
  | project i _ ih => exact .project i ih
  | record _ ih => exact .record ih
  | int => exact .int _
  | bool => exact .bool _
  | skip => exact .skip
  | bvar lookup => exact .bvar lookup
  | fvar lookup => exact .fvar lookup
  | add _ _ ihl ihr => exact .add ihl ihr
  | ge _ _ ihl ihr => exact .ge ihl ihr
  | cond _ _ _ ihc ihy ihn => exact .cond ihc ihy ihn
  | seq _ _ ihl ihr => exact .seq ihl ihr
  | loop _ _ iht ihb => exact .loop iht ihb
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | letE _ _ ihv ihb => exact .letE ihv ihb
  | letRecFun _ _ ihf ihb => exact .letRecFun ihf ihb
  | pair _ _ ihl ihr => exact .pair ihl ihr
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | matchSum _ _ _ ihe ihl ihr => exact .matchSum ihe ihl ihr
  | ref _ ih => exact .ref ih
  | assign _ _ ihl ihr => exact .assign ihl ihr
  | deref _ ih => exact .deref ih

/-- The shared L3 finite store with contents checked using subsumption. -/
structure StoreTyped (Θ : LocTypes) (s : Store) : Prop where
  domain : ∀ loc, loc ∈ Θ ↔ loc ∈ s
  contents : ∀ {loc T value}, Θ.lookup loc = some T → s.lookup loc = some value →
    HasType Θ .empty value.val T

theorem StoreTyped.ofL3 {Θ : LocTypes} {s : Store} (typed : L3.StoreTyped Θ s) :
    StoreTyped Θ s where
  domain := typed.domain
  contents typeLookup valueLookup := HasType.ofL3 (typed.contents typeLookup valueLookup)

theorem StoreTyped.empty : StoreTyped ∅ ∅ :=
  StoreTyped.ofL3 L3.StoreTyped.empty

end Silmaril.Courses.Cambridge.Subtyping
