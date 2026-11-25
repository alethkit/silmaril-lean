module

public import Silmaril.Courses.Cambridge.L2ToL3.Defs
public import Silmaril.Courses.Cambridge.L2.Metatheory.Preservation
public import Silmaril.Courses.Cambridge.L2.Metatheory.Progress
public import Silmaril.Courses.Cambridge.L2.OperationalInstitution
public import Silmaril.Courses.Cambridge.L3.OperationalInstitution

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2ToL3

variable (address : Layout)

theorem expr_rename (e : L2.Expr) (ρ : Nat → Nat) :
    expr address (e.rename ρ) = (expr address e).rename ρ := by
  induction e generalizing ρ <;> simp [L2.Expr.rename, L3.Expr.rename, expr, *]

private theorem liftSubst_expr (σ : Nat → L2.Expr) :
    (fun n => expr address (L2.Expr.liftSubst σ n)) =
      L3.Expr.liftSubst (fun n => expr address (σ n)) := by
  funext n
  cases n <;> simp [L2.Expr.liftSubst, L3.Expr.liftSubst, expr, expr_rename]

theorem expr_subst (e : L2.Expr) (σ : Nat → L2.Expr) :
    expr address (e.subst σ) = (expr address e).subst (fun n => expr address (σ n)) := by
  induction e generalizing σ <;>
    simp [L2.Expr.subst, L3.Expr.subst, expr, liftSubst_expr, *]

theorem expr_beta (body arg : L2.Expr) :
    expr address (body.beta arg) = (expr address body).beta (expr address arg) := by
  unfold L2.Expr.beta L3.Expr.beta
  rw [expr_subst]
  congr 1
  funext n
  cases n <;> rfl

theorem expr_recClosure (domain codomain : L2.Ty) (body : L2.Expr) :
    expr address (L2.Expr.recClosure domain codomain body) =
      L3.Expr.recClosure (ty domain) (ty codomain) (expr address body) := by
  simp only [L2.Expr.recClosure, L3.Expr.recClosure, expr, expr_rename]
  rfl

@[simp] theorem value_iff (e : L2.Expr) :
    L3.IsValue (expr address e) ↔ L2.IsValue e := by
  constructor
  · intro value
    cases e <;> cases value <;> constructor
  · intro value
    cases value <;> constructor

@[simp] theorem lookup_store (s : L2.Store) (loc : L2.Loc) :
    (store address s).lookup (address loc) = (L1.Store.lookup s loc).map intValue :=
  lookup_mapCells_image address intValue s loc

@[simp] theorem store_insert (s : L2.Store) (loc : L2.Loc) (n : Int) :
    store address (s.insert loc n) = (store address s).insert (address loc) (intValue n) :=
  mapCells_insert address intValue s loc n

@[simp] theorem mem_store (s : L2.Store) (loc : L2.Loc) :
    address loc ∈ store address s ↔ loc ∈ s := by
  rw [← Finmap.lookup_isSome, lookup_store, Option.isSome_map, L1.Store.lookup,
    Finmap.lookup_isSome]

theorem store_injective : Function.Injective (store address) := by
  intro s t equal
  apply Finmap.ext_lookup
  intro l
  have point := congrArg (fun m : L3.Store => m.lookup (address l)) equal
  change (store address s).lookup (address l) = (store address t).lookup (address l) at point
  rw [lookup_store, lookup_store] at point
  change (s.lookup l).map intValue = (t.lookup l).map intValue at point
  cases hl : s.lookup l <;> cases hr : t.lookup l <;> simp_all [intValue]
  all_goals simpa only [L1.Store.lookup] using hl.trans hr.symm

theorem config_injective : Function.Injective (config address) := by
  rintro ⟨e, s⟩ ⟨e', s'⟩ equal
  rw [config, config, L3.Config.mk.injEq] at equal
  exact congrArg₂ L2.Config.mk (expr_injective address equal.1) (store_injective address equal.2)

private theorem mem_mapCells {K K' A B : Type} [DecidableEq K] [DecidableEq K']
    (key : K ↪ K') (value : A → B) (s : Finmap (fun _ : K => A)) (i : K') :
    i ∈ mapCells key value s ↔ ∃ k, key k = i ∧ k ∈ s := by
  constructor
  · intro present
    obtain ⟨b, hb⟩ := Finmap.mem_iff.1 present
    obtain ⟨k, _, eq, lookup, _⟩ := (lookup_mapCells_some key value s i b).1 hb
    exact ⟨k, eq, Finmap.mem_iff.2 ⟨_, lookup⟩⟩
  · rintro ⟨k, rfl, present⟩
    obtain ⟨a, lookup⟩ := Finmap.mem_iff.1 present
    apply Finmap.mem_iff.2
    exact ⟨value a, by simp [lookup]⟩

/-- L3 store typing requires exact domain agreement. A source environment
that only covers required locations still suffices for expression typing. -/
theorem store_typed {Γ : L2.TypeEnv} {s : L2.Store}
    (domain : ∀ loc, loc ∈ Γ.locs ↔ loc ∈ s) :
    L3.StoreTyped (locTypes address Γ) (store address s) where
  domain i := by
    simp only [locTypes, store, mem_mapCells, domain]
  contents := by
    intro i T v declared present
    obtain ⟨_, _, _, _, rfl⟩ := (lookup_mapCells_some address (fun _ => L3.Ty.int) Γ.locs i T).1 declared
    obtain ⟨_, n, _, _, rfl⟩ := (lookup_mapCells_some address intValue s i v).1 present
    exact .int n

private theorem loc_typed {Γ : L2.TypeEnv} {l : L2.Loc} (present : l ∈ Γ.locs) :
    L3.HasType (locTypes address Γ) (varTypes Γ) (.loc (address l)) (.ref .int) := by
  obtain ⟨_, lookup⟩ := Finmap.mem_iff.mp present
  exact .loc (by simp [locTypes, lookup])

/-- Typing preservation includes free names, de Bruijn binders and both binders of let-rec. -/
theorem typing {Γ : L2.TypeEnv} {e : L2.Expr} {T : L2.Ty} (h : L2.HasType Γ e T) :
    L3.HasType (locTypes address Γ) (varTypes Γ) (expr address e) (ty T) := by
  induction h with
  | int n => exact .int n
  | bool b => exact .bool b
  | add _ _ hl hr => exact .add hl hr
  | ge _ _ hl hr => exact .ge hl hr
  | cond _ _ _ ht hl hr => exact .cond ht hl hr
  | assign present _ ih => exact .assign (loc_typed address present) ih
  | deref present => exact .deref (loc_typed address present)
  | skip => exact .skip
  | seq _ _ hl hr => exact .seq hl hr
  | loop _ _ ht hb => exact .loop ht hb
  | bvar lookup => exact .bvar (by simp [varTypes, lookup])
  | @fvar Γ name T lookup =>
      exact .fvar ((lookup_mapCells_image (Function.Embedding.refl _) ty Γ.free name).trans
        (congrArg (Option.map ty) lookup))
  | lam _ ih => exact .lam ih
  | app _ _ hf ha => exact .app hf ha
  | letE _ _ hv hb => exact .letE hv hb
  | letRecFun _ _ hf hb => exact .letRecFun hf hb

/-- Every original CBV step maps to one direct L3 step, even for untyped source terms. -/
theorem step {s t : L2.Config} (h : L2.Step s t) :
    L3.Step (config address s) (config address t) := by
  induction h with
  | add n m s => exact .add n m (store address s)
  | ge n m s => exact .ge n m (store address s)
  | binaryLeft _ ih => exact .binaryLeft ih
  | binaryRight v _ ih => exact .binaryRight ((value_iff address _).2 v) ih
  | deref found => exact .derefValue (value := intValue _) (by simp [found])
  | assignValue present =>
      simp only [config, expr, store_insert]
      exact .assignValue (intValue _) ((mem_store address _ _).2 present)
  | assignStep _ ih => exact .assignRight ih
  | seqSkip => exact .seqSkip
  | seqStep _ ih => exact .seqStep ih
  | ifTrue => exact .ifTrue
  | ifFalse => exact .ifFalse
  | ifStep _ ih => exact .ifStep ih
  | «while» => exact .while
  | appLeft _ ih => exact .appLeft ih
  | appRight v _ ih => exact .appRight ((value_iff address _).2 v) ih
  | appFun v =>
      simp only [config, expr, expr_beta]
      exact .appFun ((value_iff address _).2 v)
  | letStep _ ih => exact .letStep ih
  | letValue v =>
      simp only [config, expr, expr_beta]
      exact .letValue ((value_iff address _).2 v)
  | letRecFun =>
      simp only [config, expr, expr_beta, expr_recClosure]
      exact .letRecFun

theorem steps {s t : L2.Config} (h : L2.Steps s t) :
    L3.Steps (config address s) (config address t) :=
  Relation.ReflTransGen.lift (config address) (fun _ _ => step address) _ _ h

private theorem image_int {e : L2.Expr} {n : Int} (h : expr address e = .int n) :
    e = .int n := by
  cases e <;> simp_all [expr]

private theorem image_bool {e : L2.Expr} {b : Bool} (h : expr address e = .bool b) :
    e = .bool b := by
  cases e <;> simp_all [expr]

/-- A step from a typed image configuration stays in the image. A store may
have holes, since this claim only reflects steps that actually took place. -/
theorem reflect_step {Γ : L2.TypeEnv} {e : L2.Expr} {T : L2.Ty} {s : L2.Store}
    {target : L3.Config} (typed : L2.HasType Γ e T)
    (move : L3.Step (config address ⟨e, s⟩) target) :
    ∃ next, L2.Step ⟨e, s⟩ next ∧ target = config address next := by
  simp only [config] at move
  induction e generalizing T s target <;> simp only [expr] at move
  case int | bool | skip | bvar | fvar | lam => cases move
  case binary l op r ihL ihR =>
    have hl : L2.HasType Γ l .int := by cases typed <;> assumption
    have hr : L2.HasType Γ r .int := by cases typed <;> assumption
    generalize left : expr address l = l' at move
    generalize right : expr address r = r' at move
    cases move with
    | add a b =>
        obtain rfl := image_int address left
        obtain rfl := image_int address right
        exact ⟨_, .add a b s, rfl⟩
    | ge a b =>
        obtain rfl := image_int address left
        obtain rfl := image_int address right
        exact ⟨_, .ge a b s, rfl⟩
    | binaryLeft inner =>
        subst l' r'
        obtain ⟨⟨_, _⟩, moved, equal⟩ := ihL hl inner
        simp only [config, L3.Config.mk.injEq] at equal
        obtain ⟨rfl, rfl⟩ := equal
        exact ⟨_, .binaryLeft moved, rfl⟩
    | binaryRight value inner =>
        subst l' r'
        obtain ⟨⟨_, _⟩, moved, equal⟩ := ihR hr inner
        simp only [config, L3.Config.mk.injEq] at equal
        obtain ⟨rfl, rfl⟩ := equal
        exact ⟨_, .binaryRight ((value_iff address _).1 value) moved, rfl⟩
  case cond c l r ih _ _ =>
    have hc : L2.HasType Γ c .bool := by cases typed; assumption
    generalize test : expr address c = c' at move
    cases move with
    | ifTrue =>
        obtain rfl := image_bool address test
        exact ⟨_, .ifTrue, rfl⟩
    | ifFalse =>
        obtain rfl := image_bool address test
        exact ⟨_, .ifFalse, rfl⟩
    | ifStep inner =>
        subst c'
        obtain ⟨⟨_, _⟩, moved, equal⟩ := ih hc inner
        simp only [config, L3.Config.mk.injEq] at equal
        obtain ⟨rfl, rfl⟩ := equal
        exact ⟨_, .ifStep moved, rfl⟩
  case assign l rhs ih =>
    have hr : L2.HasType Γ rhs .int := by cases typed; assumption
    generalize value : expr address rhs = rhs' at move
    cases move with
    | assignLeft inner => cases inner
    | assignRight inner =>
        subst rhs'
        obtain ⟨⟨_, _⟩, moved, equal⟩ := ih hr inner
        simp only [config, L3.Config.mk.injEq] at equal
        obtain ⟨rfl, rfl⟩ := equal
        exact ⟨_, .assignStep moved, rfl⟩
    | assignValue v present =>
        have hv : L2.IsValue rhs := (value_iff address _).1 (value ▸ v.property)
        obtain ⟨n, rfl⟩ := L2.typed_integer_value hr hv
        have ev : v = intValue n := Subtype.ext value.symm
        subst v
        refine ⟨_, .assignValue ((mem_store address s l).1 present), ?_⟩
        simp [config, expr]
  case deref l =>
    cases move with
    | derefStep inner => cases inner
    | derefValue found =>
        rw [lookup_store, Option.map_eq_some_iff] at found
        obtain ⟨n, lookup, rfl⟩ := found
        exact ⟨_, .deref lookup, rfl⟩
  case seq l r ih _ =>
    have hl : L2.HasType Γ l .unit := by cases typed; assumption
    generalize left : expr address l = l' at move
    cases move with
    | seqSkip =>
        have same : l = .skip := by cases l <;> simp_all [expr]
        subst l
        exact ⟨_, .seqSkip, rfl⟩
    | seqStep inner =>
        subst l'
        obtain ⟨⟨_, _⟩, moved, equal⟩ := ih hl inner
        simp only [config, L3.Config.mk.injEq] at equal
        obtain ⟨rfl, rfl⟩ := equal
        exact ⟨_, .seqStep moved, rfl⟩
  case loop =>
    cases move
    exact ⟨_, .while, rfl⟩
  case app fn arg ihF ihA =>
    cases typed with
    | app hf ha =>
        generalize function : expr address fn = fn' at move
        cases move with
        | appLeft inner =>
            subst fn'
            obtain ⟨⟨_, _⟩, moved, equal⟩ := ihF hf inner
            simp only [config, L3.Config.mk.injEq] at equal
            obtain ⟨rfl, rfl⟩ := equal
            exact ⟨_, .appLeft moved, rfl⟩
        | appRight value inner =>
            subst fn'
            obtain ⟨⟨_, _⟩, moved, equal⟩ := ihA ha inner
            simp only [config, L3.Config.mk.injEq] at equal
            obtain ⟨rfl, rfl⟩ := equal
            exact ⟨_, .appRight ((value_iff address _).1 value) moved, rfl⟩
        | appFun value =>
            cases fn <;> simp [expr] at function
            obtain ⟨rfl, rfl⟩ := function
            exact ⟨_, .appFun ((value_iff address _).1 value), by simp [config, expr_beta]⟩
  case letE _ _ _ ih _ =>
    cases typed with
    | letE hv _ =>
        cases move with
        | letStep inner =>
            obtain ⟨⟨_, _⟩, moved, equal⟩ := ih hv inner
            simp only [config, L3.Config.mk.injEq] at equal
            obtain ⟨rfl, rfl⟩ := equal
            exact ⟨_, .letStep moved, rfl⟩
        | letValue value =>
            exact ⟨_, .letValue ((value_iff address _).1 value), by simp [config, expr_beta]⟩
  case letRecFun =>
    cases move
    exact ⟨_, .letRecFun, by simp [config, expr_beta, expr_recClosure]⟩

theorem reflect_steps {Γ : L2.TypeEnv} {s : L2.Config} {T : L2.Ty} {target : L3.Config}
    (typed : L2.HasType Γ s.expr T) (moves : L3.Steps (config address s) target) :
    ∃ next, L2.Steps s next ∧ target = config address next := by
  have invariant : ∃ next, L2.Steps s next ∧ target = config address next ∧
      L2.HasType Γ next.expr T := by
    induction moves with
    | refl => exact ⟨s, .refl, rfl, typed⟩
    | tail _ move ih =>
        obtain ⟨u, path, rfl, hu⟩ := ih
        obtain ⟨⟨_, _⟩, traced, rfl⟩ := reflect_step address hu move
        exact ⟨_, path.tail traced, rfl, traced.preserves_type hu⟩
  obtain ⟨next, path, equal, _⟩ := invariant
  exact ⟨next, path, equal⟩

theorem may_return {s t : L2.Config}
    (returns : L2.OperationalInstitution.semantics.May s (.returned t)) :
    L3.OperationalInstitution.semantics.May (config address s)
      (.returned (config address t)) := by
  obtain ⟨moves, value⟩ := (L2.OperationalInstitution.may_return_iff _ _).1 returns
  exact (L3.OperationalInstitution.may_return_iff _ _).2
    ⟨steps address moves, (value_iff address _).2 value⟩

theorem reflect_may_return {Γ : L2.TypeEnv} {s : L2.Config} {T : L2.Ty}
    {target : L3.Config} (typed : L2.HasType Γ s.expr T)
    (returns : L3.OperationalInstitution.semantics.May (config address s) (.returned target)) :
    ∃ next, L2.OperationalInstitution.semantics.May s (.returned next) ∧
      target = config address next := by
  obtain ⟨moves, value⟩ := (L3.OperationalInstitution.may_return_iff _ _).1 returns
  obtain ⟨next, path, rfl⟩ := reflect_steps address typed moves
  exact ⟨next, (L2.OperationalInstitution.may_return_iff _ _).2
    ⟨path, (value_iff address _).1 value⟩, rfl⟩

/-- Finite return observations agree on the image of an originally typed source. -/
theorem may_return_iff {Γ : L2.TypeEnv} {s t : L2.Config} {T : L2.Ty}
    (typed : L2.HasType Γ s.expr T) :
    L3.OperationalInstitution.semantics.May (config address s) (.returned (config address t)) ↔
      L2.OperationalInstitution.semantics.May s (.returned t) := by
  refine ⟨?_, may_return address⟩
  intro returns
  obtain ⟨u, observed, equal⟩ := reflect_may_return address typed returns
  exact (config_injective address equal).symm ▸ observed

theorem steps_iff {Γ : L2.TypeEnv} {s t : L2.Config} {T : L2.Ty}
    (typed : L2.HasType Γ s.expr T) :
    L3.Steps (config address s) (config address t) ↔ L2.Steps s t := by
  refine ⟨?_, steps address⟩
  intro moves
  obtain ⟨u, path, equal⟩ := reflect_steps address typed moves
  exact (config_injective address equal).symm ▸ path

theorem stuck_iff {Γ : L2.TypeEnv} {s : L2.Config} {T : L2.Ty}
    (typed : L2.HasType Γ s.expr T) :
    L3.Stuck (config address s) ↔ L2.Stuck s := by
  constructor
  · intro ⟨nonvalue, terminal⟩
    exact ⟨fun value => nonvalue ((value_iff address _).2 value),
      fun _ move => terminal _ (step address move)⟩
  · intro ⟨nonvalue, terminal⟩
    refine ⟨fun value => nonvalue ((value_iff address _).1 value), ?_⟩
    intro target move
    obtain ⟨_, source, _⟩ := reflect_step address typed move
    exact terminal _ source

theorem infinite_iff {Γ : L2.TypeEnv} {s : L2.Config} {T : L2.Ty}
    (typed : L2.HasType Γ s.expr T) :
    InfiniteTrace L3.Step (config address s) ↔ InfiniteTrace L2.Step s := by
  refine ⟨?_, InfiniteTrace.map (config address) (fun _ _ => step address)⟩
  intro trace
  apply InfiniteTrace.coinduct
    (fun c => L2.HasType Γ c.expr T ∧ InfiniteTrace L3.Step (config address c)) ?_ ⟨typed, trace⟩
  intro c entry
  obtain ⟨_, move, tail⟩ := entry.2.unfold
  obtain ⟨next, source, rfl⟩ := reflect_step address entry.1 move
  exact ⟨next, source, source.preserves_type entry.1, tail⟩

end Silmaril.Courses.Cambridge.L2ToL3
