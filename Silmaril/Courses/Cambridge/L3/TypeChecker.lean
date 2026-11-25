module

public import Silmaril.Courses.Cambridge.L3.Typing

/-! # Executable type inference for Cambridge L3 (§5.5, Exercise 31) -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

instance : DecidableEq RecordLabels := fun ⟨as, ha⟩ ⟨bs, hb⟩ =>
  decidable_of_iff (as = bs) (Iff.of_eq (RecordLabels.mk.injEq as ha bs hb).symm)

/-- Type comparison respects record label order and compares corresponding
field types. -/
def Ty.beq : Ty → Ty → Bool
  | .int, .int | .bool, .bool | .unit, .unit => true
  | .arr a b, .arr c d | .prod a b, .prod c d | .sum a b, .sum c d => a.beq c && b.beq d
  | .ref a, .ref b => a.beq b
  | .record labels as, .record other bs =>
      if h : labels = other then
        decide (∀ i : labels.Index, (as i).beq (bs (h ▸ i)) = true)
      else false
  | _, _ => false
termination_by structural a => a

theorem Ty.beq_eq_true {a b : Ty} : a.beq b = true ↔ a = b := by
  induction a generalizing b <;> cases b <;> simp_all [Ty.beq]
  case record.record labels as ih other bs =>
    by_cases h : labels = other
    · subst other
      simp only [true_and, exists_const]
      simp only [heq_eq_eq]
      exact ⟨funext, congrFun⟩
    · simp [h]

instance : DecidableEq Ty := fun a b => decidable_of_iff (a.beq b = true) Ty.beq_eq_true

/-- Lookup in the ordered field labels. -/
def RecordLabels.indexOf (labels : RecordLabels) (name : Label) : Option labels.Index :=
  labels.names.findFinIdx? (· == name)

theorem RecordLabels.indexOf_eq_some_iff {labels : RecordLabels} {name : Label} {i : labels.Index} :
    labels.indexOf name = some i ↔ labels.label i = name := by
  unfold indexOf
  rw [List.findFinIdx?_eq_some_iff]
  constructor
  · exact fun found => beq_iff_eq.mp found.1
  · intro same
    refine ⟨beq_iff_eq.mpr same, fun j earlier eq => ?_⟩
    have equal := labels.eq_of_label_eq ((beq_iff_eq.mp eq).trans same.symm)
    exact (Nat.ne_of_lt earlier) (congrArg Fin.val equal)

/-- Continue only if the inferred type equals the required type. -/
def expectType (inferred : Option Ty) (required : Ty) : Option Unit :=
  if inferred = some required then some () else none

/-- Infer the type using the annotations and ordered record fields in the
original syntax. This checker implements the core L3 judgment. -/
def infer (Θ : LocTypes) (Γ : VarTypes) : Expr → Option Ty
  | .int _ => some .int
  | .bool _ => some .bool
  | .skip => some .unit
  | .loc a => (Θ.lookup a).map Ty.ref
  | .bvar i => Γ.bound[i]?
  | .fvar name => Γ.free.lookup name
  | .binary l op r => do
      expectType (infer Θ Γ l) .int
      expectType (infer Θ Γ r) .int
      return match op with | .add => .int | .ge => .bool
  | .cond test yes no => do
      expectType (infer Θ Γ test) .bool
      let T ← infer Θ Γ yes
      expectType (infer Θ Γ no) T
      return T
  | .seq left right => do
      expectType (infer Θ Γ left) .unit
      infer Θ Γ right
  | .loop test body => do
      expectType (infer Θ Γ test) .bool
      expectType (infer Θ Γ body) .unit
      return .unit
  | .lam A body => (infer Θ (Γ.push A) body).map (Ty.arr A)
  | .app fn arg => do
      let .arr A B ← infer Θ Γ fn | none
      expectType (infer Θ Γ arg) A
      return B
  | .letE A value body => do
      expectType (infer Θ Γ value) A
      infer Θ (Γ.push A) body
  | .letRecFun A B fn body => do
      expectType (infer Θ ((Γ.push (.arr A B)).push A) fn) B
      infer Θ (Γ.push (.arr A B)) body
  | .pair l r => do
      let A ← infer Θ Γ l
      let B ← infer Θ Γ r
      return .prod A B
  | .fst e => do
      let .prod A _ ← infer Θ Γ e | none
      return A
  | .snd e => do
      let .prod _ B ← infer Θ Γ e | none
      return B
  | .inl e T => do
      let .sum A _ := T | none
      expectType (infer Θ Γ e) A
      return T
  | .inr e T => do
      let .sum _ B := T | none
      expectType (infer Θ Γ e) B
      return T
  | .matchSum e A left B right => do
      expectType (infer Θ Γ e) (.sum A B)
      let T ← infer Θ (Γ.push A) left
      expectType (infer Θ (Γ.push B) right) T
      return T
  | .record labels es =>
      let types := fun i => infer Θ Γ (es i)
      if h : ∀ i, (types i).isSome = true then
        some (.record labels (fun i => (types i).get (h i)))
      else none
  | .project e name => do
      let .record labels types ← infer Θ Γ e | none
      let i ← labels.indexOf name
      return types i
  | .ref e => (infer Θ Γ e).map Ty.ref
  | .assign lhs rhs => do
      let .ref A ← infer Θ Γ lhs | none
      expectType (infer Θ Γ rhs) A
      return .unit
  | .deref e => do
      let .ref A ← infer Θ Γ e | none
      return A
termination_by structural e => e

@[simp] private theorem expectType_bind {α : Type} {o : Option Ty} {A : Ty}
    {next : Unit → Option α} {b : α} :
    (expectType o A >>= next) = some b ↔ o = some A ∧ next () = some b := by
  by_cases h : o = some A <;> simp [expectType, h]

theorem infer_complete {Θ : LocTypes} {Γ : VarTypes} {e : Expr} {T : Ty}
    (typed : HasType Θ Γ e T) : infer Θ Γ e = some T := by
  induction typed <;> try solve | rfl | simp_all [infer, expectType]
  case project i _ ih =>
    simp [infer, ih, (RecordLabels.indexOf_eq_some_iff (i := i)).mpr rfl]

theorem infer_sound {Θ : LocTypes} (e : Expr) {Γ : VarTypes} {T : Ty}
    (result : infer Θ Γ e = some T) : HasType Θ Γ e T := by
  induction e generalizing Γ T <;> simp only [infer] at result
  case int n => cases result; exact .int n
  case bool b => cases result; exact .bool b
  case skip => cases result; exact .skip
  case bvar => exact .bvar result
  case fvar => exact .fvar result
  case loc =>
    obtain ⟨A, found, rfl⟩ := Option.map_eq_some_iff.mp result
    exact .loc found
  case ref ih =>
    obtain ⟨A, found, rfl⟩ := Option.map_eq_some_iff.mp result
    exact .ref (ih found)
  case lam ih =>
    obtain ⟨A, found, rfl⟩ := Option.map_eq_some_iff.mp result
    exact .lam (ih found)
  case binary l op r ihl ihr =>
    simp only [expectType_bind] at result
    obtain ⟨left, right, equal⟩ := result
    cases op <;> cases equal
    · exact .add (ihl left) (ihr right)
    · exact .ge (ihl left) (ihr right)
  case cond _ _ _ ihc ihy ihn =>
    obtain ⟨test, result⟩ := expectType_bind.mp result
    obtain ⟨A, yes, result⟩ := Option.bind_eq_some_iff.mp result
    obtain ⟨no, equal⟩ := expectType_bind.mp result
    cases equal
    exact .cond (ihc test) (ihy yes) (ihn no)
  case seq _ _ ihl ihr =>
    obtain ⟨left, right⟩ := expectType_bind.mp result
    exact .seq (ihl left) (ihr right)
  case loop _ _ ihc ihb =>
    simp only [expectType_bind] at result
    obtain ⟨test, body, equal⟩ := result
    cases equal
    exact .loop (ihc test) (ihb body)
  case letE _ _ _ ihv ihb =>
    obtain ⟨value, body⟩ := expectType_bind.mp result
    exact .letE (ihv value) (ihb body)
  case letRecFun _ _ _ _ ihf ihb =>
    obtain ⟨fn, body⟩ := expectType_bind.mp result
    exact .letRecFun (ihf fn) (ihb body)
  case pair _ _ ihl ihr =>
    obtain ⟨A, left, result⟩ := Option.bind_eq_some_iff.mp result
    obtain ⟨B, right, equal⟩ := Option.bind_eq_some_iff.mp result
    cases equal
    exact .pair (ihl left) (ihr right)
  case app _ _ ihf iha =>
    obtain ⟨fnType, fn, result⟩ := Option.bind_eq_some_iff.mp result
    cases fnType <;> try contradiction
    obtain ⟨arg, equal⟩ := expectType_bind.mp result
    cases equal
    exact .app (ihf fn) (iha arg)
  case fst _ ih =>
    obtain ⟨pairType, pair, result⟩ := Option.bind_eq_some_iff.mp result
    cases pairType <;> try contradiction
    cases result
    exact .fst (ih pair)
  case snd _ ih =>
    obtain ⟨pairType, pair, result⟩ := Option.bind_eq_some_iff.mp result
    cases pairType <;> try contradiction
    cases result
    exact .snd (ih pair)
  case inl _ annotation ih =>
    cases annotation <;> try contradiction
    obtain ⟨payload, equal⟩ := expectType_bind.mp result
    cases equal
    exact .inl (ih payload)
  case inr _ annotation ih =>
    cases annotation <;> try contradiction
    obtain ⟨payload, equal⟩ := expectType_bind.mp result
    cases equal
    exact .inr (ih payload)
  case matchSum _ _ _ _ _ ihe ihl ihr =>
    obtain ⟨scrutinee, result⟩ := expectType_bind.mp result
    obtain ⟨A, left, result⟩ := Option.bind_eq_some_iff.mp result
    obtain ⟨right, equal⟩ := expectType_bind.mp result
    cases equal
    exact .matchSum (ihe scrutinee) (ihl left) (ihr right)
  case record labels es ih =>
    split at result
    · rename_i present
      cases result
      exact .record (fun i => ih i (Option.some_get (present i)).symm)
    · contradiction
  case project _ _ ih =>
    obtain ⟨recordType, record, result⟩ := Option.bind_eq_some_iff.mp result
    cases recordType <;> try contradiction
    obtain ⟨i, found, equal⟩ := Option.bind_eq_some_iff.mp result
    cases equal
    have name := RecordLabels.indexOf_eq_some_iff.mp found
    rw [← name]
    exact .project i (ih record)
  case assign _ _ ihl ihr =>
    obtain ⟨lhsType, lhs, result⟩ := Option.bind_eq_some_iff.mp result
    cases lhsType <;> try contradiction
    obtain ⟨rhs, equal⟩ := expectType_bind.mp result
    cases equal
    exact .assign (ihl lhs) (ihr rhs)
  case deref _ ih =>
    obtain ⟨refType, ref, result⟩ := Option.bind_eq_some_iff.mp result
    cases refType <;> try contradiction
    cases result
    exact .deref (ih ref)

theorem infer_iff_hasType {Θ : LocTypes} {Γ : VarTypes} {e : Expr} {T : Ty} :
    infer Θ Γ e = some T ↔ HasType Θ Γ e T :=
  ⟨infer_sound e, infer_complete⟩


theorem infer_eq_none_iff {Θ : LocTypes} {Γ : VarTypes} {e : Expr} :
    infer Θ Γ e = none ↔ ∀ T, ¬ HasType Θ Γ e T := by
  cases h : infer Θ Γ e with
  | none =>
      refine ⟨fun _ T typed => ?_, fun _ => rfl⟩
      have found := infer_complete typed
      rw [h] at found
      contradiction
  | some T => exact ⟨by simp, fun rejected => (rejected T (infer_sound e h)).elim⟩

/-- Validate a supplied location typing against the entire initial store.
Cyclic references are checked using the supplied types. -/
def checkStore (Θ : LocTypes) (s : Store) : Bool :=
  decide (Θ.keys = s.keys) &&
    s.all (fun loc value => decide (infer Θ .empty value.val = Θ.lookup loc))

private theorem all_eq_true {s : Store} (test : Loc → Value → Bool) :
    s.all test = true ↔ ∀ a v, s.lookup a = some v → test a v = true := by
  unfold Finmap.all Finmap.foldl
  let : RightCommutative (fun (ok : Bool) (entry : Sigma (fun _ : Loc => Value)) =>
      ok && test entry.1 entry.2) :=
    ⟨fun _ _ _ => by simp [Bool.and_left_comm, Bool.and_comm]⟩
  have fold (entries : Multiset (Sigma (fun _ : Loc => Value))) (initial : Bool) :
      entries.foldl (fun ok entry => ok && test entry.1 entry.2) initial = true ↔
        initial = true ∧ ∀ entry ∈ entries, test entry.1 entry.2 = true := by
    induction entries using Multiset.induction_on generalizing initial with
    | empty => simp
    | cons entry entries ih => simp [Multiset.foldl_cons, ih, and_assoc]
  rw [fold]
  simp only [true_and]
  constructor
  · intro checked a v lookup
    exact checked ⟨a, v⟩ (Finmap.lookup_eq_some_iff.mp lookup)
  · rintro checked ⟨a, v⟩ present
    exact checked a v (Finmap.lookup_eq_some_iff.mpr present)

theorem checkStore_eq_true_iff {Θ : LocTypes} {s : Store} :
    checkStore Θ s = true ↔ StoreTyped Θ s := by
  simp only [checkStore, Bool.and_eq_true, decide_eq_true_eq, all_eq_true]
  constructor
  · rintro ⟨keys, checked⟩
    refine ⟨fun loc => ?_, fun {loc T v} typeFound valFound => ?_⟩
    · rw [← Finmap.mem_keys, keys, Finmap.mem_keys]
    · exact infer_sound _ ((checked loc v valFound).trans typeFound)
  · intro typed
    refine ⟨Finset.ext (fun loc => Finmap.mem_keys.trans
      ((typed.domain loc).trans Finmap.mem_keys.symm)), ?_⟩
    intro loc v valFound
    obtain ⟨T, typeFound⟩ := Finmap.mem_iff.mp
      ((typed.domain loc).mpr (Finmap.mem_of_lookup_eq_some valFound))
    exact (infer_complete (typed.contents typeFound valFound)).trans typeFound.symm

end Silmaril.Courses.Cambridge.L3
