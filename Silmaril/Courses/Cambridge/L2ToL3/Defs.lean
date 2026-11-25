module

public import Silmaril.Courses.Cambridge.L2.Typing
public import Silmaril.Courses.Cambridge.L3.Typing
public import Mathlib.Logic.Equiv.List

/-! Resolved CBV syntax with an injective layout for the statically named L2
integer cells. L3 locations hold integers in the image of a source store. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2ToL3

abbrev Layout := L2.Loc ↪ L3.Loc

/-- A concrete layout obtained by encoding the list of Unicode scalar values. -/
def unicodeLayout : Layout where
  toFun name := Encodable.encode (name.toList.map Char.toNat)
  inj' := fun _ _ h => String.toList_injective
    ((List.map_injective_iff.2 (fun _ _ eq => Char.toNat_inj.1 eq))
      (Encodable.encode_injective h))

def ty : L2.Ty → L3.Ty
  | .int => .int
  | .bool => .bool
  | .unit => .unit
  | .arr domain codomain => .arr (ty domain) (ty codomain)

variable (address : Layout)

def expr : L2.Expr → L3.Expr
  | .int n => .int n
  | .bool b => .bool b
  | .binary l op r => .binary (expr l) op (expr r)
  | .cond c l r => .cond (expr c) (expr l) (expr r)
  | .assign loc rhs => .assign (.loc (address loc)) (expr rhs)
  | .deref loc => .deref (.loc (address loc))
  | .skip => .skip
  | .seq l r => .seq (expr l) (expr r)
  | .loop test body => .loop (expr test) (expr body)
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .lam domain body => .lam (ty domain) (expr body)
  | .app fn arg => .app (expr fn) (expr arg)
  | .letE type value body => .letE (ty type) (expr value) (expr body)
  | .letRecFun domain codomain fn body =>
      .letRecFun (ty domain) (ty codomain) (expr fn) (expr body)

@[simp] theorem ty_inj {a b : L2.Ty} : ty a = ty b ↔ a = b := by
  induction a generalizing b <;> cases b <;> simp_all [ty]

@[simp] theorem expr_inj {a b : L2.Expr} : expr address a = expr address b ↔ a = b := by
  induction a generalizing b <;> cases b <;> simp [expr, address.injective.eq_iff, *]

theorem expr_injective : Function.Injective (expr address) := fun _ _ => (expr_inj address).1

/-- Apply one map to the keys and one to the values of a finite partial map. -/
def mapCells {K K' A B : Type} (key : K ↪ K') (value : A → B)
    (s : Finmap (fun _ : K => A)) : Finmap (fun _ : K' => B) :=
  ⟨s.entries.map (fun cell => ⟨key cell.1, value cell.2⟩), by
    rw [← Multiset.nodup_keys]
    change (Multiset.map Sigma.fst (s.entries.map _)).Nodup
    have nodup := Multiset.Nodup.map key.injective s.nodupKeys.nodup_keys
    simpa only [Multiset.keys, Multiset.map_map, Function.comp_def] using nodup⟩

theorem lookup_mapCells_some {K K' A B : Type} [DecidableEq K] [DecidableEq K']
    (key : K ↪ K') (value : A → B) (s : Finmap (fun _ : K => A)) (k : K') (b : B) :
    (mapCells key value s).lookup k = some b ↔
      ∃ source a, key source = k ∧ s.lookup source = some a ∧ value a = b := by
  rw [Finmap.lookup_eq_some_iff]
  change _ ∈ s.entries.map _ ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨⟨source, a⟩, member, equal⟩
    exact ⟨source, a, congrArg Sigma.fst equal, Finmap.lookup_eq_some_iff.mpr member,
      congrArg (fun p : Sigma (fun _ : K' => B) => p.2) equal⟩
  · rintro ⟨source, a, rfl, lookup, rfl⟩
    exact ⟨⟨source, a⟩, Finmap.lookup_eq_some_iff.mp lookup, rfl⟩

@[simp] theorem lookup_mapCells_image {K K' A B : Type} [DecidableEq K] [DecidableEq K']
    (key : K ↪ K') (value : A → B) (s : Finmap (fun _ : K => A)) (k : K) :
    (mapCells key value s).lookup (key k) = (s.lookup k).map value := by
  cases lookup : s.lookup k with
  | none =>
      cases target : (mapCells key value s).lookup (key k) with
      | none => rfl
      | some b =>
          obtain ⟨source, _, same, found, _⟩ := (lookup_mapCells_some key value s _ _).1 target
          cases key.injective same
          simp [lookup] at found
  | some a => exact (lookup_mapCells_some key value s _ _).2 ⟨k, a, rfl, lookup, rfl⟩

theorem mapCells_insert {K K' A B : Type} [DecidableEq K] [DecidableEq K']
    (key : K ↪ K') (value : A → B) (s : Finmap (fun _ : K => A)) (k : K) (a : A) :
    mapCells key value (s.insert k a) = (mapCells key value s).insert (key k) (value a) := by
  apply Finmap.ext_lookup
  intro i
  by_cases h : i = key k
  · subst i
    simp
  · rw [Finmap.lookup_insert_of_ne _ h]
    apply Option.ext
    intro b
    simp only [lookup_mapCells_some]
    apply exists_congr
    intro source
    apply exists_congr
    intro v
    apply and_congr_right
    intro same
    rw [Finmap.lookup_insert_of_ne]
    intro equal
    exact h (same.symm.trans (congrArg key equal))

def intValue (n : Int) : L3.Value := ⟨.int n, .int n⟩

def store (s : L2.Store) : L3.Store := mapCells address intValue s

def locTypes (Γ : L2.TypeEnv) : L3.LocTypes :=
  mapCells address (fun _ => .int) Γ.locs

def varTypes (Γ : L2.TypeEnv) : L3.VarTypes :=
  ⟨mapCells (Function.Embedding.refl _) ty Γ.free, Γ.bound.map ty⟩

def config (c : L2.Config) : L3.Config := ⟨expr address c.expr, store address c.store⟩

end Silmaril.Courses.Cambridge.L2ToL3
