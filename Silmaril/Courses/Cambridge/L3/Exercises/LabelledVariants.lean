module

public import Silmaril.Courses.Cambridge.L3.Metatheory.Substitution
import Silmaril.Courses.Cambridge.L3.Metatheory.SubstitutionAlgebra
public import Silmaril.Courses.Cambridge.L3.Reduction

/-! # Exercise 29: labelled variants

Design for §5.6, p. 82 of the 12 February 2026 notes. A nonempty variant
has one payload type per distinct label and one binding branch per label.
Injections and exhaustive matches elaborate to L3 sums and strict let.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Exercises.LabelledVariants

inductive Row where
  | last (label : Label) (payload : Ty)
  | cons (label : Label) (payload : Ty) (tail : Row)

def Row.labels : Row → List Label
  | .last name _ => [name]
  | .cons name _ tail => name :: tail.labels

/-- Exercise-local variant types retain their labels and source order. -/
structure VariantType where
  row : Row
  distinct : row.labels.Nodup

/-- A reference to a declared label, indexed by its payload type. -/
inductive Tag : Row → Ty → Type where
  | last {name : Label} {A : Ty} : Tag (.last name A) A
  | head {name : Label} {A : Ty} {tail : Row} : Tag (.cons name A tail) A
  | rest {name : Label} {A B : Ty} {tail : Row} : Tag tail B → Tag (.cons name A tail) B

def Tag.label {row : Row} {A : Ty} : Tag row A → Label
  | @Tag.last name _ => name
  | @Tag.head name _ _ => name
  | .rest tag => tag.label

/-- Resolve a written label to the corresponding payload type and tag. -/
def Row.find : (row : Row) → Label → Option (Σ A, Tag row A)
  | .last name A, query => if query = name then some ⟨A, .last⟩ else none
  | .cons name A tail, query =>
      if query = name then some ⟨A, .head⟩
      else (tail.find query).map fun ⟨B, tag⟩ => ⟨B, .rest tag⟩

private theorem Tag.label_mem {row : Row} {A : Ty} (tag : Tag row A) :
    tag.label ∈ row.labels := by
  induction tag with
  | last => simp [Row.labels, Tag.label]
  | head => simp [Row.labels, Tag.label]
  | rest _ ih => exact List.mem_cons_of_mem _ ih

theorem Tag.find_label {row : Row} {A : Ty} (tag : Tag row A) (distinct : row.labels.Nodup) :
    row.find tag.label = some ⟨A, tag⟩ := by
  induction tag with
  | last => simp [Row.find, Tag.label]
  | head => simp [Row.find, Tag.label]
  | @rest name _ _ tail tag ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp distinct
    have different : tag.label ≠ name := fun equal => absent (equal ▸ tag.label_mem)
    simp [Row.find, Tag.label, different, ih unique]

def Row.carrier : Row → Ty
  | .last _ A => A
  | .cons _ A tail => .sum A tail.carrier

def Tag.inject {row : Row} {A : Ty} (tag : Tag row A) (payload : Expr) : Expr :=
  match tag with
  | .last => payload
  | .head => .inl payload row.carrier
  | .rest tag => .inr (tag.inject payload) row.carrier

/-- The abstract syntax of a labelled injection. -/
structure Injection (T : VariantType) where
  payloadType : Ty
  tag : Tag T.row payloadType
  payload : Expr

/-- Each branch has one local binder for the payload of its own tag. -/
abbrev Branches (row : Row) := ∀ {A}, Tag row A → Expr

/-- The abstract syntax of an exhaustive labelled match. -/
structure Match (T : VariantType) where
  scrutinee : Expr
  branches : Branches T.row

def Row.dispatch : (row : Row) → Expr → Branches row → Expr
  | .last _ A, e, branches => .letE A e (branches .last)
  | .cons _ A tail, e, branches =>
      .matchSum e A (branches .head) tail.carrier
        (tail.dispatch (.bvar 0) (fun tag => (branches (.rest tag)).rename (DeBruijn.lift Nat.succ)))

def Injection.lower {T : VariantType} (e : Injection T) : Expr := e.tag.inject e.payload

def Match.lower {T : VariantType} (e : Match T) : Expr := T.row.dispatch e.scrutinee e.branches

theorem Tag.inject_typed {row : Row} {A : Ty} (tag : Tag row A)
    {Θ : LocTypes} {Γ : VarTypes} {payload : Expr} (typed : HasType Θ Γ payload A) :
    HasType Θ Γ (tag.inject payload) row.carrier := by
  induction tag with
  | last => exact typed
  | head => exact .inl typed
  | rest _ ih => exact .inr (ih typed)

/-- Injection checks the payload against the selected label's declared type. -/
theorem Injection.lower_typed {T : VariantType} (e : Injection T)
    {Θ : LocTypes} {Γ : VarTypes} (typed : HasType Θ Γ e.payload e.payloadType) :
    HasType Θ Γ e.lower T.row.carrier :=
  e.tag.inject_typed typed

/-- Match checks each branch under its own payload binder and a common result type. -/
theorem Row.dispatch_typed (row : Row) {Θ : LocTypes} {Γ : VarTypes} {e : Expr}
    {branches : Branches row} {T : Ty} (scrutinee : HasType Θ Γ e row.carrier)
    (bodies : ∀ {A} (tag : Tag row A), HasType Θ (Γ.push A) (branches tag) T) :
    HasType Θ Γ (row.dispatch e branches) T := by
  induction row generalizing Γ e with
  | last => exact .letE scrutinee (bodies .last)
  | cons _ A tail ih =>
    refine .matchSum scrutinee (bodies .head) (ih (.bvar rfl) ?_)
    intro B tag
    exact (bodies (.rest tag)).rename _ rfl (BoundRenaming.push (BoundRenaming.succ Γ.bound tail.carrier) B)

theorem Match.lower_typed {T : VariantType} (e : Match T)
    {Θ : LocTypes} {Γ : VarTypes} {B : Ty}
    (scrutinee : HasType Θ Γ e.scrutinee T.row.carrier)
    (bodies : ∀ {A} (tag : Tag T.row A), HasType Θ (Γ.push A) (e.branches tag) B) :
    HasType Θ Γ e.lower B :=
  T.row.dispatch_typed scrutinee bodies

theorem Tag.inject_value {row : Row} {A : Ty} (tag : Tag row A)
    {payload : Expr} (ready : IsValue payload) : IsValue (tag.inject payload) := by
  induction tag with
  | last => exact ready
  | head => exact .inl ready
  | rest _ ih => exact .inr ih

/-- Injection retains the CBV evaluation and store effects of its payload. -/
theorem Tag.inject_step {row : Row} {A : Ty} (tag : Tag row A)
    {e e' : Expr} {s s' : Store} (step : Step ⟨e, s⟩ ⟨e', s'⟩) :
    Step ⟨tag.inject e, s⟩ ⟨tag.inject e', s'⟩ := by
  induction tag with
  | last => exact step
  | head => exact .inl step
  | rest _ ih => exact .inr ih

theorem Row.dispatch_step (row : Row) {branches : Branches row}
    {e e' : Expr} {s s' : Store} (step : Step ⟨e, s⟩ ⟨e', s'⟩) :
    Step ⟨row.dispatch e branches, s⟩ ⟨row.dispatch e' branches, s'⟩ := by
  cases row with
  | last => exact .letStep step
  | cons => exact .matchStep step

private theorem subst_under_skip (body : Expr) (σ : Nat → Expr) :
    (body.rename (DeBruijn.lift Nat.succ)).subst (Expr.liftSubst (Expr.liftSubst σ)) =
      (body.subst (Expr.liftSubst σ)).rename (DeBruijn.lift Nat.succ) := by
  rw [Expr.subst_rename, Expr.rename_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [Function.comp_apply, DeBruijn.lift, Expr.liftSubst, Expr.rename_comp]
    rfl

private theorem dispatch_subst (row : Row) (e : Expr) (branches : Branches row) (σ : Nat → Expr) :
    (row.dispatch e branches).subst σ =
      row.dispatch (e.subst σ) (fun tag => (branches tag).subst (Expr.liftSubst σ)) := by
  induction row generalizing e σ with
  | last => rfl
  | cons _ _ tail ih =>
    simp only [Row.dispatch, Expr.subst, ih, Expr.liftSubst]
    congr 1
    congr 1
    funext A tag
    exact subst_under_skip _ _

private theorem dispatch_beta (row : Row) (payload : Expr) (branches : Branches row) :
    (row.dispatch (.bvar 0) (fun tag => (branches tag).rename (DeBruijn.lift Nat.succ))).beta payload =
      row.dispatch payload branches := by
  rw [Expr.beta, dispatch_subst]
  change row.dispatch payload _ = row.dispatch payload _
  congr 1
  funext A tag
  rw [Expr.subst_rename]
  conv_rhs => rw [← Expr.subst_id (branches tag)]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => rfl

/-- Once the payload is a value, only the matching branch runs. The branch
receives the original payload with capture-avoiding substitution. -/
theorem Tag.dispatch_inject {row : Row} {A : Ty} (tag : Tag row A)
    {payload : Expr} (ready : IsValue payload) (branches : Branches row) (s : Store) :
    Steps ⟨row.dispatch (tag.inject payload) branches, s⟩ ⟨(branches tag).beta payload, s⟩ := by
  induction tag with
  | last => exact .single (.letValue ready)
  | head => exact .single (.matchLeft ready)
  | rest tag ih =>
    apply Relation.ReflTransGen.head (.matchRight (tag.inject_value ready))
    rw [dispatch_beta]
    exact ih (fun tag => branches (.rest tag))

def input : VariantType :=
  ⟨.cons "number" .int (.cons "ready" .bool (.last "done" .unit)), by
    simp [Row.labels]⟩

def exampleInjection : Injection input :=
  ⟨.bool, .rest .head, .binary (.int 7) .ge (.int 4)⟩

def exampleMatch : Match input :=
  ⟨exampleInjection.lower, fun
    | .head => .bvar 0
    | .rest .head => .cond (.bvar 0) (.int 42) (.int 0)
    | .rest (.rest .last) => .int 0⟩

theorem example_tag_resolves :
    input.row.find "ready" = some ⟨.bool, .rest .head⟩ := rfl

theorem undeclared_tag_rejected :
    input.row.find "missing" = none := rfl

theorem example_typed : HasType ∅ .empty exampleMatch.lower .int := by
  apply exampleMatch.lower_typed (exampleInjection.lower_typed (.ge (.int 7) (.int 4)))
  intro A tag
  cases tag with
  | head => exact .bvar rfl
  | rest tag =>
    cases tag with
    | head => exact .cond (.bvar rfl) (.int 42) (.int 0)
    | rest tag => cases tag; exact .int 0

theorem example_returns (s : Store) : Steps ⟨exampleMatch.lower, s⟩ ⟨.int 42, s⟩ := by
  have payload : Step ⟨exampleInjection.payload, s⟩ ⟨.bool true, s⟩ := .ge 7 4 s
  refine .head (input.row.dispatch_step (exampleInjection.tag.inject_step payload)) ?_
  exact (exampleInjection.tag.dispatch_inject (.bool true) exampleMatch.branches s).tail .ifTrue

end Silmaril.Courses.Cambridge.L3.Exercises.LabelledVariants
