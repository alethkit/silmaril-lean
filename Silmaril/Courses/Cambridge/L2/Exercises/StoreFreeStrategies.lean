module

public import Silmaril.Courses.Cambridge.L2.FullBeta
public import Silmaril.Courses.Cambridge.L2.Denotation.Pure
import Silmaril.Courses.Cambridge.L2.Denotation.Operational
import Silmaril.Courses.Cambridge.L2.Metatheory.Interpreter
import Silmaril.Courses.Cambridge.L2.Metatheory.NameInterpreter

/-! # Cambridge L2 Exercise 23, without store operations

A common interpretation into total values suffices to compare successful
results of the two strategies on closed, well-typed terms without reads,
writes or recursive bindings. A loop has type unit, so it can be interpreted
as unit even when its evaluation diverges. The proof uses invariance under
individual steps. It makes no termination inference from the interpretation.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.Exercises.StoreFreeStrategies

open PureDenotation (Env Value)

/-- The fragment excludes reads, assignments and recursive bindings at every
depth. In particular, it includes while loops and higher-order functions. -/
def Fragment : Expr → Prop
  | .deref _ | .assign _ _ | .letRecFun _ _ _ _ => False
  | .int _ | .bool _ | .skip | .bvar _ | .fvar _ => True
  | .binary e _ f | .seq e f | .loop e f | .app e f | .letE _ e f =>
      Fragment e ∧ Fragment f
  | .cond test yes no => Fragment test ∧ Fragment yes ∧ Fragment no
  | .lam _ e => Fragment e

/-- A typed interpretation for comparing finite results. Unit computations
carry no data here, so sequence discards its first operand's value and every
well-typed loop denotes unit. -/
private inductive Interprets : (Γ : List Ty) → Expr → (T : Ty) → (Env Γ → Value T) → Prop
  | int {Γ : List Ty} (n : Int) : Interprets Γ (.int n) .int (fun _ => n)
  | bool {Γ : List Ty} (b : Bool) : Interprets Γ (.bool b) .bool (fun _ => b)
  | skip {Γ : List Ty} : Interprets Γ .skip .unit (fun _ => ())
  | add {Γ : List Ty} {e f : Expr} {left right : Env Γ → Int} :
      Interprets Γ e .int left → Interprets Γ f .int right →
      Interprets Γ (.binary e .add f) .int (fun ρ => left ρ + right ρ)
  | ge {Γ : List Ty} {e f : Expr} {left right : Env Γ → Int} :
      Interprets Γ e .int left → Interprets Γ f .int right →
      Interprets Γ (.binary e .ge f) .bool (fun ρ => decide (left ρ ≥ right ρ))
  | cond {Γ : List Ty} {test yes no : Expr} {T : Ty} {guard : Env Γ → Bool}
      {onTrue onFalse : Env Γ → Value T} : Interprets Γ test .bool guard → Interprets Γ yes T onTrue →
      Interprets Γ no T onFalse →
      Interprets Γ (.cond test yes no) T (fun ρ => if guard ρ then onTrue ρ else onFalse ρ)
  | seq {Γ : List Ty} {e f : Expr} {T : Ty} {ignored : Env Γ → Unit}
      {result : Env Γ → Value T} : Interprets Γ e .unit ignored → Interprets Γ f T result →
      Interprets Γ (.seq e f) T result
  | loop {Γ : List Ty} {test body : Expr} {guard : Env Γ → Bool} {ignored : Env Γ → Unit} :
      Interprets Γ test .bool guard → Interprets Γ body .unit ignored →
      Interprets Γ (.loop test body) .unit (fun _ => ())
  | bvar {Γ : List Ty} {i : Nat} {T : Ty} (lookup : Γ[i]? = some T) :
      Interprets Γ (.bvar i) T (fun ρ => ρ.lookup lookup)
  | lam {Γ : List Ty} {A B : Ty} {body : Expr} {result : Env (A :: Γ) → Value B} :
      Interprets (A :: Γ) body B result →
      Interprets Γ (.lam A body) (.arr A B) (fun ρ v => result (ρ.push v))
  | app {Γ : List Ty} {fn arg : Expr} {A B : Ty} {function : Env Γ → Value A → Value B}
      {argument : Env Γ → Value A} : Interprets Γ fn (.arr A B) function → Interprets Γ arg A argument →
      Interprets Γ (.app fn arg) B (fun ρ => function ρ (argument ρ))
  | letE {Γ : List Ty} {e body : Expr} {A B : Ty} {value : Env Γ → Value A}
      {result : Env (A :: Γ) → Value B} : Interprets Γ e A value → Interprets (A :: Γ) body B result →
      Interprets Γ (.letE A e body) B (fun ρ => result (ρ.push (value ρ)))

private theorem interpretation {Γ : TypeEnv} {e : Expr} {T : Ty}
    (typed : HasType Γ e T) (fragment : Fragment e) (free : Γ.free = ∅) :
    ∃ meaning, Interprets Γ.bound e T meaning := by
  induction typed with
  | int n => exact ⟨_, .int n⟩
  | bool b => exact ⟨_, .bool b⟩
  | skip => exact ⟨_, .skip⟩
  | bvar lookup => exact ⟨_, .bvar lookup⟩
  | fvar lookup => simp [free] at lookup
  | assign | deref | letRecFun => exact False.elim fragment
  | lam _ ih =>
    obtain ⟨_, body⟩ := ih fragment free
    exact ⟨_, .lam body⟩
  | cond _ _ _ ihTest ihYes ihNo =>
    obtain ⟨_, test⟩ := ihTest fragment.1 free
    obtain ⟨_, yes⟩ := ihYes fragment.2.1 free
    obtain ⟨_, no⟩ := ihNo fragment.2.2 free
    exact ⟨_, .cond test yes no⟩
  | add _ _ ihLeft ihRight | ge _ _ ihLeft ihRight | seq _ _ ihLeft ihRight
  | loop _ _ ihLeft ihRight | app _ _ ihLeft ihRight | letE _ _ ihLeft ihRight =>
    obtain ⟨_, left⟩ := ihLeft fragment.1 free
    obtain ⟨_, right⟩ := ihRight fragment.2 free
    first | exact ⟨_, .add left right⟩ | exact ⟨_, .ge left right⟩
          | exact ⟨_, .seq left right⟩ | exact ⟨_, .loop left right⟩
          | exact ⟨_, .app left right⟩ | exact ⟨_, .letE left right⟩

private def Renaming (Γ Δ : List Ty) (rename : Nat → Nat) (env : Env Δ → Env Γ) : Prop :=
  ∀ {i T} (lookup : Γ[i]? = some T),
    ∃ target : Δ[rename i]? = some T, ∀ ρ, (env ρ).lookup lookup = ρ.lookup target

private theorem Renaming.push {Γ Δ : List Ty} {rename : Nat → Nat} {env : Env Δ → Env Γ}
    (compatible : Renaming Γ Δ rename env) (A : Ty) :
    Renaming (A :: Γ) (A :: Δ) (DeBruijn.lift rename) (fun ρ => (env ρ.2).push ρ.1) := by
  intro i T lookup
  cases i with
  | zero => exact ⟨lookup, fun _ => rfl⟩
  | succ i =>
    obtain ⟨target, same⟩ := compatible (i := i) (by simpa using lookup)
    exact ⟨by simpa [DeBruijn.lift] using target, fun ρ => same ρ.2⟩

private theorem Interprets.rename {Γ Δ : List Ty} {e : Expr} {T : Ty} {value : Env Γ → Value T}
    (term : Interprets Γ e T value) (rename : Nat → Nat) (env : Env Δ → Env Γ)
    (compatible : Renaming Γ Δ rename env) :
    Interprets Δ (e.rename rename) T (fun ρ => value (env ρ)) := by
  induction term generalizing Δ rename with
  | int n => exact .int n
  | bool b => exact .bool b
  | skip => exact .skip
  | bvar lookup =>
    obtain ⟨target, same⟩ := compatible lookup
    simpa only [Expr.rename, same] using (Interprets.bvar target)
  | add _ _ left right => exact .add (left rename env compatible) (right rename env compatible)
  | ge _ _ left right => exact .ge (left rename env compatible) (right rename env compatible)
  | seq _ _ left right => exact .seq (left rename env compatible) (right rename env compatible)
  | loop _ _ guard body => exact .loop (guard rename env compatible) (body rename env compatible)
  | cond _ _ _ guard yes no =>
    exact .cond (guard rename env compatible) (yes rename env compatible) (no rename env compatible)
  | lam _ body => exact .lam (body _ _ (compatible.push _))
  | app _ _ fn arg => exact .app (fn rename env compatible) (arg rename env compatible)
  | letE _ _ value body => exact .letE (value rename env compatible) (body _ _ (compatible.push _))

private def Substitution (Γ Δ : List Ty) (σ : Nat → Expr) (env : Env Δ → Env Γ) : Prop :=
  ∀ {i T} (lookup : Γ[i]? = some T), Interprets Δ (σ i) T (fun ρ => (env ρ).lookup lookup)

private theorem Substitution.push {Γ Δ : List Ty} {σ : Nat → Expr} {env : Env Δ → Env Γ}
    (compatible : Substitution Γ Δ σ env) (A : Ty) :
    Substitution (A :: Γ) (A :: Δ) (Expr.liftSubst σ) (fun ρ => (env ρ.2).push ρ.1) := by
  intro i T lookup
  cases i with
  | zero =>
    exact .bvar (Γ := A :: Δ) (i := 0) (by simpa using lookup)
  | succ i =>
    exact (compatible (i := i) lookup).rename (Δ := A :: Δ) Nat.succ (fun ρ => ρ.2)
      (fun lookup => ⟨by simpa using lookup, fun _ => rfl⟩)

private theorem Interprets.subst {Γ Δ : List Ty} {e : Expr} {T : Ty} {value : Env Γ → Value T}
    (term : Interprets Γ e T value) (σ : Nat → Expr) (env : Env Δ → Env Γ)
    (compatible : Substitution Γ Δ σ env) :
    Interprets Δ (e.subst σ) T (fun ρ => value (env ρ)) := by
  induction term generalizing Δ σ with
  | int n => exact .int n
  | bool b => exact .bool b
  | skip => exact .skip
  | bvar lookup => exact compatible lookup
  | add _ _ left right => exact .add (left σ env compatible) (right σ env compatible)
  | ge _ _ left right => exact .ge (left σ env compatible) (right σ env compatible)
  | seq _ _ left right => exact .seq (left σ env compatible) (right σ env compatible)
  | loop _ _ guard body => exact .loop (guard σ env compatible) (body σ env compatible)
  | cond _ _ _ guard yes no =>
    exact .cond (guard σ env compatible) (yes σ env compatible) (no σ env compatible)
  | lam _ body => exact .lam (body _ _ (compatible.push _))
  | app _ _ fn arg => exact .app (fn σ env compatible) (arg σ env compatible)
  | letE _ _ value body => exact .letE (value σ env compatible) (body _ _ (compatible.push _))

private theorem Interprets.beta {Γ : List Ty} {body argument : Expr} {A B : Ty}
    {fn : Env (A :: Γ) → Value B} {arg : Env Γ → Value A}
    (bodyMeaning : Interprets (A :: Γ) body B fn) (argMeaning : Interprets Γ argument A arg) :
    Interprets Γ (body.beta argument) B (fun ρ => fn (ρ.push (arg ρ))) := by
  apply bodyMeaning.subst
  intro i T lookup
  cases i with
  | zero =>
    cases Option.some.inj lookup
    exact argMeaning
  | succ i => exact .bvar (Γ := Γ) (i := i) (by simpa using lookup)

private theorem Interprets.nameStep {before after : Config} (step : NameStep before after)
    {Γ : List Ty} {T : Ty} {meaning : Env Γ → Value T}
    (term : Interprets Γ before.expr T meaning) : Interprets Γ after.expr T meaning := by
  induction step generalizing Γ T with
  | add m n =>
    cases term with
    | add left right => cases left; cases right; exact .int (m + n)
  | ge m n =>
    cases term with
    | ge left right => cases left; cases right; exact .bool (m ≥ n)
  | binaryLeft _ ih =>
    cases term with
    | add left right => exact .add (ih left) right
    | ge left right => exact .ge (ih left) right
  | binaryRight _ _ ih =>
    cases term with
    | add left right => exact .add left (ih right)
    | ge left right => exact .ge left (ih right)
  | deref | assignValue | assignStep | letRecFun => cases term
  | seqSkip => cases term with | seq _ right => exact right
  | seqStep _ ih => cases term with | seq left right => exact .seq (ih left) right
  | ifTrue =>
    cases term with
    | cond test yes no => cases test; exact yes
  | ifFalse =>
    cases term with
    | cond test yes no => cases test; exact no
  | ifStep _ ih =>
    cases term with
    | cond test yes no => exact .cond (ih test) yes no
  | «while» =>
    cases term with
    | loop test body =>
      have unrolled := Interprets.cond test (.seq body (.loop test body)) .skip
      simpa only [ite_self] using unrolled
  | appLeft _ ih =>
    cases term with
    | app fn arg => exact .app (ih fn) arg
  | appFun =>
    cases term with
    | app fn arg =>
      cases fn with
      | lam body => exact body.beta arg
  | letStep _ ih => cases term with | letE value body => exact .letE (ih value) body
  | letValue => cases term with | letE value body => exact body.beta value

private theorem Interprets.betaStep {before after : Config} (step : BetaStep before after)
    {Γ : List Ty} {T : Ty} {meaning : Env Γ → Value T}
    (term : Interprets Γ before.expr T meaning) : Interprets Γ after.expr T meaning := by
  induction step generalizing Γ T with
  | name step => exact term.nameStep step
  | binaryLeft _ ih =>
    cases term with
    | add left right => exact .add (ih left) right
    | ge left right => exact .ge (ih left) right
  | binaryRight _ _ ih =>
    cases term with
    | add left right => exact .add left (ih right)
    | ge left right => exact .ge left (ih right)
  | assignStep => cases term
  | seqStep _ ih => cases term with | seq left right => exact .seq (ih left) right
  | ifStep _ ih =>
    cases term with
    | cond test yes no => exact .cond (ih test) yes no
  | appLeft _ ih => cases term with | app fn arg => exact .app (ih fn) arg
  | appRight _ ih => cases term with | app fn arg => exact .app fn (ih arg)
  | lamBody _ ih => cases term with | lam body => exact .lam (ih body)
  | letStep _ ih => cases term with | letE value body => exact .letE (ih value) body

private theorem Interprets.betaSteps {before after : Config} (run : BetaSteps before after)
    {Γ : List Ty} {T : Ty} {meaning : Env Γ → Value T}
    (term : Interprets Γ before.expr T meaning) : Interprets Γ after.expr T meaning := by
  induction run with
  | refl => exact term
  | tail _ step ih => exact ih.betaStep step

private theorem Interprets.bool_eq {b : Bool} {meaning : Env [] → Bool}
    (term : Interprets [] (.bool b) .bool meaning) : meaning Env.empty = b := by
  cases term
  rfl

/-- For closed typed inputs in the fragment, successful CBV and CBN Boolean
returns agree. The two runs may start with any stores. -/
theorem bool_returns_agree {e : Expr} {valueResult nameResult : Bool}
    {valueInitial valueFinal nameInitial nameFinal : Store}
    (typed : HasType TypeEnv.empty e .bool) (fragment : Fragment e)
    (cbv : Steps ⟨e, valueInitial⟩ ⟨.bool valueResult, valueFinal⟩)
    (cbn : NameSteps ⟨e, nameInitial⟩ ⟨.bool nameResult, nameFinal⟩) :
    valueResult = nameResult := by
  obtain ⟨_, term⟩ := interpretation typed fragment rfl
  exact (term.betaSteps (valueSteps_imply_beta cbv)).bool_eq.symm.trans
    (term.betaSteps (nameSteps_imply_beta cbn)).bool_eq

/-- Exercise 23 specializes the agreement theorem to applying a typed
function to `skip`. -/
theorem applied_to_skip_agrees {fn : Expr} {valueResult nameResult : Bool} {s t u : Store}
    (typed : HasType TypeEnv.empty fn (.arr .unit .bool)) (fragment : Fragment fn)
    (cbv : Steps ⟨.app fn .skip, s⟩ ⟨.bool valueResult, t⟩)
    (cbn : NameSteps ⟨.app fn .skip, s⟩ ⟨.bool nameResult, u⟩) :
    valueResult = nameResult :=
  bool_returns_agree (.app typed .skip) ⟨fragment, trivial⟩ cbv cbn

/-! ## Two terminating runs and a termination difference -/

/-- Bind a function with strict let and pass it a terminating loop. CBV
executes the loop, while CBN skips it because the parameter is unused. -/
def returnsAfterLoop : Expr :=
  .lam .unit (.letE (.arr .unit .bool) (.lam .unit (.bool true))
    (.app (.bvar 0) (.loop (.bool false) .skip)))

theorem returnsAfterLoop_checks :
    HasType TypeEnv.empty returnsAfterLoop (.arr .unit .bool) ∧ Fragment returnsAfterLoop :=
  ⟨infer_sound _ _ (by decide), by simp [returnsAfterLoop, Fragment]⟩

theorem terminating_loop_returns (s : Store) :
    Steps ⟨.app returnsAfterLoop .skip, s⟩ ⟨.bool true, s⟩ ∧
      NameSteps ⟨.app returnsAfterLoop .skip, s⟩ ⟨.bool true, s⟩ :=
  ⟨(runFuel_value_returns_terminal (fuel := 10) rfl).1,
    (runFuel_name_returns_terminal (fuel := 10) rfl).1⟩

def divergingLoop : Expr := .loop (.bool true) .skip

private theorem forever_infinite (s : Store) : InfiniteTrace Step ⟨divergingLoop, s⟩ := by
  let start : Config := ⟨divergingLoop, s⟩
  let unrolled : Config := ⟨.cond (.bool true) (.seq .skip divergingLoop) .skip, s⟩
  let body : Config := ⟨.seq .skip divergingLoop, s⟩
  apply InfiniteTrace.coinduct
    (fun c => c = start ∨ c = unrolled ∨ c = body) ?_ (Or.inl rfl)
  rintro c (rfl | rfl | rfl)
  · exact ⟨unrolled, .while, Or.inr (Or.inl rfl)⟩
  · exact ⟨body, .ifTrue, Or.inr (Or.inr rfl)⟩
  · exact ⟨start, .seqSkip, Or.inl rfl⟩

def ignoresForever : Expr :=
  .lam .unit (.app (.lam .unit (.bool true)) divergingLoop)

theorem ignoresForever_checks :
    HasType TypeEnv.empty ignoresForever (.arr .unit .bool) ∧ Fragment ignoresForever :=
  ⟨infer_sound _ _ (by decide), by simp [ignoresForever, divergingLoop, Fragment]⟩

theorem name_returns_ignoring_loop (s : Store) :
    NameSteps ⟨.app ignoresForever .skip, s⟩ ⟨.bool true, s⟩ :=
  (Relation.ReflTransGen.single NameStep.appFun).tail NameStep.appFun

theorem value_diverges_on_loop (s : Store) :
    InfiniteTrace Step ⟨.app ignoresForever .skip, s⟩ := by
  refine InfiniteTrace.fold (b := ⟨.app (.lam .unit (.bool true)) divergingLoop, s⟩)
    (.appFun .skip) ?_
  exact (forever_infinite s).map
    (fun (c : Config) => (⟨.app (.lam .unit (.bool true)) c.expr, c.store⟩ : Config))
    (fun _ _ step => Step.appRight (.lam _ _) step)

/-- The CBV observation in this example is divergence along actual steps. -/
theorem value_has_no_return (s : Store) (result : Config) (value : IsValue result.expr) :
    ¬ Steps ⟨.app ignoresForever .skip, s⟩ result := by
  intro path
  exact RightUnique.not_infinite_of_final Denotation.stepRightUnique path
    (value_terminal value) (value_diverges_on_loop s)

end Silmaril.Courses.Cambridge.L2.Exercises.StoreFreeStrategies
