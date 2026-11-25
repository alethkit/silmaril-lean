module

public import Silmaril.Courses.Cambridge.L2.FullBeta
public import Silmaril.Courses.Cambridge.L2.Denotation.Pure
import Silmaril.Semantics.Domain.Function
import Silmaril.Courses.Cambridge.L2.Denotation.Operational
import Silmaril.Courses.Cambridge.L2.Metatheory.Interpreter
import Silmaril.Courses.Cambridge.L2.Metatheory.NameInterpreter

/-! # Cambridge L2 Exercise 23, without store operations

The two source strategies embed in the existing full-beta relation.
On store-free syntax every step preserves a common typed interpretation
in flat domains and continuous function spaces. Recursive closures and
while loops use least fixed points in those domains. Substitution
preserves meaning even for an unevaluated argument. This suffices to
compare successful results without turning denotations into termination
claims for either strategy.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.Exercises.StoreFreeStrategies

open OmegaCompletePartialOrder Semantics.Domain

/-- The original fragment excludes reads, assignments and recursive
bindings at every depth. -/
def Fragment : Expr → Prop
  | .deref _ | .assign _ _ | .letRecFun _ _ _ _ => False
  | .int _ | .bool _ | .skip | .bvar _ | .fvar _ => True
  | .binary e _ f | .seq e f | .loop e f | .app e f | .letE _ e f =>
      Fragment e ∧ Fragment f
  | .cond test yes no => Fragment test ∧ Fragment yes ∧ Fragment no
  | .lam _ e => Fragment e

/-- Store-free syntax excludes reads and assignments at every depth. -/
def StoreFree : Expr → Prop
  | .deref _ | .assign _ _ => False
  | .int _ | .bool _ | .skip | .bvar _ | .fvar _ => True
  | .binary e _ f | .seq e f | .loop e f | .app e f | .letE _ e f | .letRecFun _ _ e f =>
      StoreFree e ∧ StoreFree f
  | .cond test yes no => StoreFree test ∧ StoreFree yes ∧ StoreFree no
  | .lam _ e => StoreFree e

theorem Fragment.storeFree {e : Expr} (fragment : Fragment e) : StoreFree e := by
  induction e <;> simp_all [Fragment, StoreFree]

@[reducible] private noncomputable def Val : Ty → DomainCat
  | .int => .of (Part Int)
  | .bool => .of (Part Bool)
  | .unit => .of (Part Unit)
  | .arr A B => .of (Val A →𝒄 Val B)

@[reducible] private noncomputable def Env : List Ty → DomainCat
  | [] => .of (Part Unit)
  | A :: Γ => .of (Val A × Env Γ)

private abbrev Meaning (Γ : List Ty) (T : Ty) := Env Γ →𝒄 Val T

private noncomputable def lookupHom : {Γ : List Ty} → {i : Nat} → {T : Ty} →
    Γ[i]? = some T → Meaning Γ T
  | [], _, _, lookup => by simp at lookup
  | _ :: _, 0, _, lookup => by cases Option.some.inj lookup; exact fstHom
  | _ :: Γ, i + 1, _, lookup => (lookupHom (Γ := Γ) (i := i) lookup).comp sndHom

private noncomputable def liftEnv {Γ Δ : List Ty} (A : Ty) (env : Env Δ →𝒄 Env Γ) :
    Env (A :: Δ) →𝒄 Env (A :: Γ) :=
  pairHom fstHom (env.comp sndHom)

private noncomputable def binaryHom {Γ : List Ty} {X : Type} (op : Int → Int → X)
    (left right : Meaning Γ .int) : Env Γ →𝒄 Part X :=
  left.bind (piHom fun n => ContinuousHom.map (op n) right)

private noncomputable def condHom {Γ : List Ty} {T : Ty} (test : Meaning Γ .bool)
    (yes no : Meaning Γ T) : Meaning Γ T :=
  cond.comp (pairHom test (pairHom yes no))

private noncomputable def seqHom {Γ : List Ty} {T : Ty} (left : Meaning Γ .unit)
    (right : Meaning Γ T) : Meaning Γ T :=
  condHom ((Flat.map fun _ : Unit => true).comp left) right ⊥

private noncomputable def whileFunctional {Γ : List Ty} (test : Meaning Γ .bool)
    (body : Meaning Γ .unit) : Env Γ →𝒄 Val .unit →𝒄 Val .unit :=
  curry ((condHom (Γ := .unit :: Γ) (test.comp sndHom)
    (seqHom (body.comp sndHom) fstHom) (ContinuousHom.const (Part.some ()))).comp
    (pairHom sndHom fstHom))

private noncomputable def whileHom {Γ : List Ty} (test : Meaning Γ .bool)
    (body : Meaning Γ .unit) : Meaning Γ .unit :=
  fixHom.comp (whileFunctional test body)

private theorem whileHom_unfold {Γ : List Ty} (test : Meaning Γ .bool)
    (body : Meaning Γ .unit) :
    condHom test (seqHom body (whileHom test body)) (ContinuousHom.const (Part.some ())) =
      whileHom test body :=
  ContinuousHom.ext _ _ fun ρ => fix_eq (whileFunctional test body ρ)

private noncomputable def lamHom {Γ : List Ty} {A B : Ty} (body : Meaning (A :: Γ) B) :
    Meaning Γ (.arr A B) :=
  curry (body.comp (pairHom sndHom fstHom))

private noncomputable def appHom {Γ : List Ty} {A B : Ty} (fn : Meaning Γ (.arr A B))
    (arg : Meaning Γ A) : Meaning Γ B :=
  evalHom'.comp (pairHom fn arg)

private noncomputable def letHom {Γ : List Ty} {A B : Ty} (value : Meaning Γ A)
    (body : Meaning (A :: Γ) B) : Meaning Γ B :=
  body.comp (pairHom value ContinuousHom.id)

private noncomputable def recFunctional {Γ : List Ty} {A B : Ty}
    (code : Meaning (A :: .arr A B :: Γ) B) : Env Γ →𝒄 Val (.arr A B) →𝒄 Val (.arr A B) :=
  curry (curry
    (code.comp (pairHom sndHom (pairHom (sndHom.comp fstHom) (fstHom.comp fstHom)))))

/-- Fix the function denotation with its lexical environment as a parameter. -/
private noncomputable def recHom {Γ : List Ty} {A B : Ty}
    (code : Meaning (A :: .arr A B :: Γ) B) : Meaning Γ (.arr A B) :=
  fixHom.comp (recFunctional code)

private theorem recHom_unfold {Γ : List Ty} {A B : Ty}
    (code : Meaning (A :: .arr A B :: Γ) B) (ρ : Env Γ) (arg : Val A) :
    recHom code ρ arg = code (arg, recHom code ρ, ρ) :=
  (congrArg (fun f : Val (.arr A B) => f arg) (fix_eq (recFunctional code ρ))).symm

private theorem whileHom_comp {Γ Δ : List Ty} (test : Meaning Γ .bool)
    (body : Meaning Γ .unit) (env : Env Δ →𝒄 Env Γ) :
    whileHom (test.comp env) (body.comp env) = (whileHom test body).comp env := by
  refine ContinuousHom.ext _ _ fun ρ => ?_
  change fix (whileFunctional (test.comp env) (body.comp env) ρ) =
    fix (whileFunctional test body (env ρ))
  apply congrArg fix
  exact ContinuousHom.ext _ _ fun _ => rfl

private theorem recHom_comp {Γ Δ : List Ty} {A B : Ty}
    (code : Meaning (A :: .arr A B :: Γ) B) (env : Env Δ →𝒄 Env Γ) :
    recHom (code.comp (liftEnv A (liftEnv (.arr A B) env))) = (recHom code).comp env := by
  refine ContinuousHom.ext _ _ fun ρ => ?_
  change fix (recFunctional (code.comp (liftEnv A (liftEnv (.arr A B) env))) ρ) =
    fix (recFunctional code (env ρ))
  apply congrArg fix
  exact ContinuousHom.ext _ _ fun _ => ContinuousHom.ext _ _ fun _ => rfl

/-- A typing derivation with a continuous meaning in the pure model. -/
private inductive Interprets : (Γ : List Ty) → Expr → (T : Ty) → Meaning Γ T → Prop
  | int {Γ : List Ty} (n : Int) :
      Interprets Γ (.int n) .int (ContinuousHom.const (Part.some n))
  | bool {Γ : List Ty} (b : Bool) :
      Interprets Γ (.bool b) .bool (ContinuousHom.const (Part.some b))
  | skip {Γ : List Ty} :
      Interprets Γ .skip .unit (ContinuousHom.const (Part.some ()))
  | add {Γ : List Ty} {e f : Expr} {left right : Meaning Γ .int} :
      Interprets Γ e .int left → Interprets Γ f .int right →
      Interprets Γ (.binary e .add f) .int (binaryHom (· + ·) left right)
  | ge {Γ : List Ty} {e f : Expr} {left right : Meaning Γ .int} :
      Interprets Γ e .int left → Interprets Γ f .int right →
      Interprets Γ (.binary e .ge f) .bool (binaryHom (fun a b => decide (a ≥ b)) left right)
  | cond {Γ : List Ty} {test yes no : Expr} {T : Ty} {guard : Meaning Γ .bool}
      {onTrue onFalse : Meaning Γ T} : Interprets Γ test .bool guard → Interprets Γ yes T onTrue →
      Interprets Γ no T onFalse →
      Interprets Γ (.cond test yes no) T (condHom guard onTrue onFalse)
  | seq {Γ : List Ty} {e f : Expr} {T : Ty} {left : Meaning Γ .unit}
      {right : Meaning Γ T} : Interprets Γ e .unit left → Interprets Γ f T right →
      Interprets Γ (.seq e f) T (seqHom left right)
  | loop {Γ : List Ty} {test body : Expr} {guard : Meaning Γ .bool} {action : Meaning Γ .unit} :
      Interprets Γ test .bool guard → Interprets Γ body .unit action →
      Interprets Γ (.loop test body) .unit (whileHom guard action)
  | bvar {Γ : List Ty} {i : Nat} {T : Ty} (lookup : Γ[i]? = some T) :
      Interprets Γ (.bvar i) T (lookupHom lookup)
  | lam {Γ : List Ty} {A B : Ty} {body : Expr} {result : Meaning (A :: Γ) B} :
      Interprets (A :: Γ) body B result →
      Interprets Γ (.lam A body) (.arr A B) (lamHom result)
  | app {Γ : List Ty} {fn arg : Expr} {A B : Ty} {function : Meaning Γ (.arr A B)}
      {argument : Meaning Γ A} : Interprets Γ fn (.arr A B) function → Interprets Γ arg A argument →
      Interprets Γ (.app fn arg) B (appHom function argument)
  | letE {Γ : List Ty} {e body : Expr} {A B : Ty} {value : Meaning Γ A}
      {result : Meaning (A :: Γ) B} : Interprets Γ e A value → Interprets (A :: Γ) body B result →
      Interprets Γ (.letE A e body) B (letHom value result)
  | letRecFun {Γ : List Ty} {A B T : Ty} {code body : Expr}
      {function : Meaning (A :: .arr A B :: Γ) B} {result : Meaning (.arr A B :: Γ) T} :
      Interprets (A :: .arr A B :: Γ) code B function → Interprets (.arr A B :: Γ) body T result →
      Interprets Γ (.letRecFun A B code body) T (letHom (recHom function) result)

private theorem interpretation {Γ : TypeEnv} {e : Expr} {T : Ty}
    (typed : HasType Γ e T) (fragment : StoreFree e) (free : Γ.free = ∅) :
    ∃ meaning, Interprets Γ.bound e T meaning := by
  induction typed with
  | int n => exact ⟨_, .int n⟩
  | bool b => exact ⟨_, .bool b⟩
  | skip => exact ⟨_, .skip⟩
  | bvar lookup => exact ⟨_, .bvar lookup⟩
  | fvar lookup => simp [free] at lookup
  | assign | deref => exact False.elim fragment
  | lam _ ih =>
    obtain ⟨_, body⟩ := ih fragment free
    exact ⟨_, .lam body⟩
  | cond _ _ _ ihTest ihYes ihNo =>
    obtain ⟨_, test⟩ := ihTest fragment.1 free
    obtain ⟨_, yes⟩ := ihYes fragment.2.1 free
    obtain ⟨_, no⟩ := ihNo fragment.2.2 free
    exact ⟨_, .cond test yes no⟩
  | add _ _ ihLeft ihRight | ge _ _ ihLeft ihRight | seq _ _ ihLeft ihRight
  | loop _ _ ihLeft ihRight | app _ _ ihLeft ihRight | letE _ _ ihLeft ihRight
  | letRecFun _ _ ihLeft ihRight =>
    obtain ⟨_, left⟩ := ihLeft fragment.1 free
    obtain ⟨_, right⟩ := ihRight fragment.2 free
    first | exact ⟨_, .add left right⟩ | exact ⟨_, .ge left right⟩
          | exact ⟨_, .seq left right⟩ | exact ⟨_, .loop left right⟩
          | exact ⟨_, .app left right⟩ | exact ⟨_, .letE left right⟩
          | exact ⟨_, .letRecFun left right⟩

private def Renaming (Γ Δ : List Ty) (rename : Nat → Nat) (env : Env Δ →𝒄 Env Γ) : Prop :=
  ∀ {i T} (lookup : Γ[i]? = some T),
    ∃ target : Δ[rename i]? = some T, (lookupHom lookup).comp env = lookupHom target

private theorem Renaming.push {Γ Δ : List Ty} {rename : Nat → Nat} {env : Env Δ →𝒄 Env Γ}
    (compatible : Renaming Γ Δ rename env) (A : Ty) :
    Renaming (A :: Γ) (A :: Δ) (DeBruijn.lift rename) (liftEnv A env) := by
  intro i T lookup
  cases i with
  | zero =>
    have same : A = T := by simpa using lookup
    subst T
    exact ⟨lookup, rfl⟩
  | succ i =>
    obtain ⟨target, same⟩ := compatible (i := i) (by simpa using lookup)
    refine ⟨by simpa [DeBruijn.lift] using target, ContinuousHom.ext _ _ fun ρ => ?_⟩
    exact congrArg (fun f : Meaning Δ T => f ρ.2) same

private theorem Interprets.rename {Γ Δ : List Ty} {e : Expr} {T : Ty} {value : Meaning Γ T}
    (term : Interprets Γ e T value) (rename : Nat → Nat) (env : Env Δ →𝒄 Env Γ)
    (compatible : Renaming Γ Δ rename env) :
    Interprets Δ (e.rename rename) T (value.comp env) := by
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
  | loop _ _ guard body =>
    have lifted := Interprets.loop (guard rename env compatible) (body rename env compatible)
    rw [whileHom_comp] at lifted
    exact lifted
  | cond _ _ _ guard yes no =>
    exact .cond (guard rename env compatible) (yes rename env compatible) (no rename env compatible)
  | lam _ body => exact .lam (body _ _ (compatible.push _))
  | app _ _ fn arg => exact .app (fn rename env compatible) (arg rename env compatible)
  | letE _ _ value body => exact .letE (value rename env compatible) (body _ _ (compatible.push _))
  | letRecFun _ _ code body =>
    have lifted := Interprets.letRecFun (code _ _ (Renaming.push (Renaming.push compatible _) _))
      (body _ _ (compatible.push _))
    unfold letHom at lifted
    rw [recHom_comp] at lifted
    exact lifted

private def Substitution (Γ Δ : List Ty) (σ : Nat → Expr) (env : Env Δ →𝒄 Env Γ) : Prop :=
  ∀ {i T} (lookup : Γ[i]? = some T), Interprets Δ (σ i) T ((lookupHom lookup).comp env)

private theorem Substitution.push {Γ Δ : List Ty} {σ : Nat → Expr} {env : Env Δ →𝒄 Env Γ}
    (compatible : Substitution Γ Δ σ env) (A : Ty) :
    Substitution (A :: Γ) (A :: Δ) (Expr.liftSubst σ) (liftEnv A env) := by
  intro i T lookup
  cases i with
  | zero =>
    have same : A = T := by simpa using lookup
    subst T
    exact .bvar (Γ := A :: Δ) (i := 0) rfl
  | succ i =>
    exact (compatible (i := i) lookup).rename (Δ := A :: Δ) Nat.succ sndHom
      (fun lookup => ⟨by simpa using lookup, rfl⟩)

private theorem Interprets.subst {Γ Δ : List Ty} {e : Expr} {T : Ty} {value : Meaning Γ T}
    (term : Interprets Γ e T value) (σ : Nat → Expr) (env : Env Δ →𝒄 Env Γ)
    (compatible : Substitution Γ Δ σ env) :
    Interprets Δ (e.subst σ) T (value.comp env) := by
  induction term generalizing Δ σ with
  | int n => exact .int n
  | bool b => exact .bool b
  | skip => exact .skip
  | bvar lookup => exact compatible lookup
  | add _ _ left right => exact .add (left σ env compatible) (right σ env compatible)
  | ge _ _ left right => exact .ge (left σ env compatible) (right σ env compatible)
  | seq _ _ left right => exact .seq (left σ env compatible) (right σ env compatible)
  | loop _ _ guard body =>
    have lifted := Interprets.loop (guard σ env compatible) (body σ env compatible)
    rw [whileHom_comp] at lifted
    exact lifted
  | cond _ _ _ guard yes no =>
    exact .cond (guard σ env compatible) (yes σ env compatible) (no σ env compatible)
  | lam _ body => exact .lam (body _ _ (compatible.push _))
  | app _ _ fn arg => exact .app (fn σ env compatible) (arg σ env compatible)
  | letE _ _ value body => exact .letE (value σ env compatible) (body _ _ (compatible.push _))
  | letRecFun _ _ code body =>
    have lifted := Interprets.letRecFun (code _ _ (Substitution.push (Substitution.push compatible _) _))
      (body _ _ (compatible.push _))
    unfold letHom at lifted
    rw [recHom_comp] at lifted
    exact lifted

private theorem Interprets.beta {Γ : List Ty} {body argument : Expr} {A B : Ty}
    {fn : Meaning (A :: Γ) B} {arg : Meaning Γ A}
    (bodyMeaning : Interprets (A :: Γ) body B fn) (argMeaning : Interprets Γ argument A arg) :
    Interprets Γ (body.beta argument) B (letHom arg fn) := by
  apply bodyMeaning.subst _ (pairHom arg ContinuousHom.id)
  intro i T lookup
  cases i with
  | zero =>
    cases Option.some.inj lookup
    exact argMeaning
  | succ i => exact .bvar (Γ := Γ) (i := i) (by simpa using lookup)

private theorem Renaming.shift (Γ : List Ty) (A : Ty) :
    Renaming Γ (A :: Γ) Nat.succ sndHom := by
  intro i T lookup
  exact ⟨by simpa using lookup, rfl⟩

private noncomputable def swapEnv {Γ : List Ty} {A B : Ty} :
    Env (B :: A :: Γ) →𝒄 Env (A :: B :: Γ) :=
  pairHom (fstHom.comp sndHom) (pairHom fstHom (sndHom.comp sndHom))

private theorem Renaming.swap (Γ : List Ty) (A B : Ty) :
    Renaming (A :: B :: Γ) (B :: A :: Γ) swapFirstTwo swapEnv := by
  intro i T lookup
  cases i with
  | zero =>
    have same : A = T := by simpa using lookup
    subst T
    exact ⟨rfl, rfl⟩
  | succ i =>
    cases i with
    | zero =>
      have same : B = T := by simpa using lookup
      subst T
      exact ⟨rfl, rfl⟩
    | succ i =>
      exact ⟨by simpa [swapFirstTwo] using lookup, rfl⟩

/-- The original L2 closure re-enters its binding under the parameter.
The two source renamings respectively weaken the saved code and swap
the parameter with the freshly installed recursive name. -/
private theorem Interprets.recClosure {Γ : List Ty} {A B : Ty} {body : Expr}
    {code : Meaning (A :: .arr A B :: Γ) B}
    (interprets : Interprets (A :: .arr A B :: Γ) body B code) :
    Interprets Γ (Expr.recClosure A B body) (.arr A B) (recHom code) := by
  have shifted := interprets.rename _ _ (Renaming.push (Renaming.push (Renaming.shift Γ A) (.arr A B)) A)
  have swapped := interprets.rename _ _ (Renaming.swap Γ A (.arr A B))
  have closure := Interprets.lam (.letRecFun shifted swapped)
  have closureMeaning :
      lamHom (letHom (recHom (code.comp (liftEnv A (liftEnv (.arr A B) sndHom))))
        (code.comp swapEnv)) = recHom code := by
    refine ContinuousHom.ext _ _ fun ρ => ContinuousHom.ext _ _ fun arg => ?_
    -- The saved code ignores the extra parameter in the renewed binding.
    rw [recHom_comp]
    exact (recHom_unfold code ρ arg).symm
  rw [closureMeaning] at closure
  exact closure

private theorem binaryHom_const {Γ : List Ty} {X : Type} (op : Int → Int → X) (a b : Int) :
    binaryHom (Γ := Γ) op (ContinuousHom.const (Part.some a))
      (ContinuousHom.const (Part.some b)) = ContinuousHom.const (Part.some (op a b)) := by
  refine ContinuousHom.ext _ _ fun _ => ?_
  change (Part.some a).bind (fun x => (Part.some b).map (op x)) = Part.some (op a b)
  simp

private theorem condHom_true {Γ : List Ty} {T : Ty} (yes no : Meaning Γ T) :
    condHom (ContinuousHom.const (Part.some true)) yes no = yes :=
  ContinuousHom.ext _ _ fun ρ => condFun_true (yes ρ) (no ρ)

private theorem condHom_false {Γ : List Ty} {T : Ty} (yes no : Meaning Γ T) :
    condHom (ContinuousHom.const (Part.some false)) yes no = no :=
  ContinuousHom.ext _ _ fun ρ => condFun_false (yes ρ) (no ρ)

private theorem seqHom_skip {Γ : List Ty} {T : Ty} (right : Meaning Γ T) :
    seqHom (ContinuousHom.const (Part.some ())) right = right := by
  refine ContinuousHom.ext _ _ fun ρ => ?_
  change condFun (Flat.map (fun _ : Unit => true) (Part.some ())) (right ρ) ⊥ = right ρ
  rw [Flat.map_some, condFun_true]

private theorem Interprets.nameStep {before after : Config} (step : NameStep before after)
    {Γ : List Ty} {T : Ty} {meaning : Meaning Γ T}
    (term : Interprets Γ before.expr T meaning) : Interprets Γ after.expr T meaning := by
  induction step generalizing Γ T with
  | add m n =>
    cases term with
    | add left right =>
      cases left
      cases right
      rw [binaryHom_const]
      exact .int (m + n)
  | ge m n =>
    cases term with
    | ge left right =>
      cases left
      cases right
      rw [binaryHom_const]
      exact .bool (m ≥ n)
  | binaryLeft _ ih =>
    cases term with
    | add left right => exact .add (ih left) right
    | ge left right => exact .ge (ih left) right
  | binaryRight _ _ ih =>
    cases term with
    | add left right => exact .add left (ih right)
    | ge left right => exact .ge left (ih right)
  | deref | assignValue | assignStep => cases term
  | seqSkip =>
    cases term with
    | seq left right =>
      cases left
      rwa [seqHom_skip]
  | seqStep _ ih => cases term with | seq left right => exact .seq (ih left) right
  | ifTrue =>
    cases term with
    | cond test yes no =>
      cases test
      rwa [condHom_true]
  | ifFalse =>
    cases term with
    | cond test yes no =>
      cases test
      rwa [condHom_false]
  | ifStep _ ih =>
    cases term with
    | cond test yes no => exact .cond (ih test) yes no
  | «while» =>
    cases term with
    | loop test body =>
      have unrolled := Interprets.cond test (.seq body (.loop test body)) .skip
      rwa [whileHom_unfold] at unrolled
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

  | letRecFun =>
    cases term with
    | letRecFun code body => exact body.beta code.recClosure

private theorem Interprets.betaStep {before after : Config} (step : BetaStep before after)
    {Γ : List Ty} {T : Ty} {meaning : Meaning Γ T}
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
    {Γ : List Ty} {T : Ty} {meaning : Meaning Γ T}
    (term : Interprets Γ before.expr T meaning) : Interprets Γ after.expr T meaning := by
  induction run with
  | refl => exact term
  | tail _ step ih => exact ih.betaStep step

private theorem Interprets.bool_eq {b : Bool} {meaning : Meaning [] .bool}
    (term : Interprets [] (.bool b) .bool meaning) : meaning ⊥ = Part.some b := by
  cases term
  rfl

/-- Any two successful Boolean returns in the original CBV and CBN
relations agree on closed typed store-free syntax. Recursion and loops
are interpreted by least fixed points. Both initial stores are arbitrary. -/
theorem storeFree_bool_returns_agree {e : Expr} {valueResult nameResult : Bool}
    {valueInitial valueFinal nameInitial nameFinal : Store}
    (typed : HasType TypeEnv.empty e .bool) (storeFree : StoreFree e)
    (cbv : Steps ⟨e, valueInitial⟩ ⟨.bool valueResult, valueFinal⟩)
    (cbn : NameSteps ⟨e, nameInitial⟩ ⟨.bool nameResult, nameFinal⟩) :
    valueResult = nameResult := by
  obtain ⟨_, term⟩ := interpretation typed storeFree rfl
  exact Part.some_inj.mp ((term.betaSteps (valueSteps_imply_beta cbv)).bool_eq.symm.trans
    (term.betaSteps (nameSteps_imply_beta cbn)).bool_eq)

/-- Exercise 23 for a closed typed store-free function applied to `skip`. -/
theorem storeFree_applied_to_skip_agrees {fn : Expr} {valueResult nameResult : Bool}
    {s t u : Store}
    (typed : HasType TypeEnv.empty fn (.arr .unit .bool)) (storeFree : StoreFree fn)
    (cbv : Steps ⟨.app fn .skip, s⟩ ⟨.bool valueResult, t⟩)
    (cbn : NameSteps ⟨.app fn .skip, s⟩ ⟨.bool nameResult, u⟩) :
    valueResult = nameResult :=
  storeFree_bool_returns_agree (.app typed .skip) ⟨storeFree, trivial⟩ cbv cbn

/-- Agreement on the original recursion-free fragment. -/
theorem bool_returns_agree {e : Expr} {valueResult nameResult : Bool}
    {valueInitial valueFinal nameInitial nameFinal : Store}
    (typed : HasType TypeEnv.empty e .bool) (fragment : Fragment e)
    (cbv : Steps ⟨e, valueInitial⟩ ⟨.bool valueResult, valueFinal⟩)
    (cbn : NameSteps ⟨e, nameInitial⟩ ⟨.bool nameResult, nameFinal⟩) :
    valueResult = nameResult :=
  storeFree_bool_returns_agree typed fragment.storeFree cbv cbn

theorem applied_to_skip_agrees {fn : Expr} {valueResult nameResult : Bool} {s t u : Store}
    (typed : HasType TypeEnv.empty fn (.arr .unit .bool)) (fragment : Fragment fn)
    (cbv : Steps ⟨.app fn .skip, s⟩ ⟨.bool valueResult, t⟩)
    (cbn : NameSteps ⟨.app fn .skip, s⟩ ⟨.bool nameResult, u⟩) :
    valueResult = nameResult :=
  storeFree_applied_to_skip_agrees typed fragment.storeFree cbv cbn

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

/-! ## A successful recursive call under both strategies -/

/-- The function binds a threshold, counts down from three by calling
itself, then checks the threshold saved outside the recursive binder. -/
def recursiveCountdown : Expr :=
  .lam .unit (.letE .int (.int 2)
    (.letRecFun .int .bool
      (.cond (.binary (.bvar 0) .ge (.int 1))
        (.app (.bvar 1) (.binary (.bvar 0) .add (.int (-1))))
        (.binary (.bvar 2) .ge (.int 2)))
      (.app (.bvar 0) (.int 3))))

theorem recursiveCountdown_checks :
    HasType TypeEnv.empty recursiveCountdown (.arr .unit .bool) ∧ StoreFree recursiveCountdown :=
  ⟨infer_sound _ _ (by decide), by simp [recursiveCountdown, StoreFree]⟩

theorem recursive_countdown_returns (s : Store) :
    Steps ⟨.app recursiveCountdown .skip, s⟩ ⟨.bool true, s⟩ ∧
      NameSteps ⟨.app recursiveCountdown .skip, s⟩ ⟨.bool true, s⟩ :=
  ⟨(runFuel_value_returns_terminal (fuel := 50) rfl).1,
    (runFuel_name_returns_terminal (fuel := 50) rfl).1⟩

end Silmaril.Courses.Cambridge.L2.Exercises.StoreFreeStrategies
