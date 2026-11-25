module

public import Silmaril.Courses.Cambridge.L2.Denotation.Relational.Defs
public import Silmaril.Courses.Cambridge.L2.Reduction
import Silmaril.Courses.Cambridge.L2.Denotation.Relational.Finite
import Silmaril.Courses.Cambridge.L2.Denotation.Substitution

/-! # Finite adequacy of the L2 closure denotation

The saved environment is substituted only when comparing the semantic
closure with a value expression. The evaluation rules operate on the
environment directly.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.RelationalDenotation

open PureDenotation (extendSubst beta_after_subst recClosure_body_beta recClosure_enter)

mutual
  /-- Reify a value using the source lambda and recursive closure forms. -/
  def quote : RuntimeValue → Expr
    | .int n => .int n
    | .bool b => .bool b
    | .unit => .skip
    | .closure A body saved => .lam A (body.subst (Expr.liftSubst (quoteEnv saved)))
    | .recursive A B body saved =>
        Expr.recClosure A B (body.subst (Expr.liftSubst (Expr.liftSubst (quoteEnv saved))))

  /-- Discharge the captured binders in nearest-first order. Remaining indices
  refer to the ambient binders beyond the saved environment. -/
  def quoteEnv : RuntimeEnv → Nat → Expr
    | [], i => .bvar i
    | v :: _, 0 => quote v
    | _ :: ρ, i + 1 => quoteEnv ρ i
end

private theorem quoteEnv_cons (v : RuntimeValue) (ρ : RuntimeEnv) :
    quoteEnv (v :: ρ) = extendSubst (quote v) (quoteEnv ρ) := by
  funext i
  cases i <;> simp [quoteEnv, extendSubst]

private theorem quoteEnv_lookup (ρ : RuntimeEnv) (i : Nat) :
    quoteEnv ρ i = ((ρ[i]?).map quote).getD (.bvar (i - ρ.length)) := by
  induction ρ generalizing i with
  | nil => simp [quoteEnv]
  | cons v ρ ih =>
    cases i with
    | zero => simp [quoteEnv]
    | succ i => simpa [quoteEnv] using ih i

theorem quote_isValue (v : RuntimeValue) : IsValue (quote v) := by
  cases v <;> simp only [quote, Expr.recClosure] <;> constructor

private theorem Returns.sound {ρ : RuntimeEnv} {e : Expr} {s t : Store} {v : RuntimeValue}
    (run : Returns ρ e s v t) : SubstitutionReturn (e.subst (quoteEnv ρ)) s ⟨quote v, t⟩ := by
  induction run with
  | int n => exact .value (.int n)
  | bool b => exact .value (.bool b)
  | skip => exact .value .skip
  | @var ρ i v s lookup =>
    simpa [Expr.subst, quoteEnv_lookup, lookup] using
      (SubstitutionReturn.value (s := s) (quote_isValue v))
  | lam => exact .value (.lam _ _)
  | add _ _ left right => exact .add left right
  | ge _ _ left right => exact .ge left right
  | deref lookup => exact .deref lookup
  | assign _ present rhs => exact .assign rhs present
  | seq _ _ first second => exact .seq first second
  | ifTrue _ _ test yes => exact .ifTrue test yes
  | ifFalse _ _ test no => exact .ifFalse test no
  | whileFalse _ test => exact .whileFalse test
  | whileTrue _ _ _ test body rest => exact .whileTrue test body rest
  | app _ _ _ fn arg body =>
    refine .app fn arg ?_
    rwa [beta_after_subst, ← quoteEnv_cons]
  | appRec _ _ _ fn arg body =>
    simp only [quote, Expr.recClosure] at fn
    refine .app fn arg ?_
    rw [recClosure_body_beta]
    apply SubstitutionReturn.letRec
    rw [recClosure_enter]
    simpa only [quoteEnv_cons, quote] using body
  | letE _ _ rhs body =>
    refine .letE rhs ?_
    rwa [beta_after_subst, ← quoteEnv_cons]
  | letRec _ body =>
    apply SubstitutionReturn.letRec
    rw [beta_after_subst]
    simpa only [quoteEnv_cons, quote] using body

private def valueOrIndex : Expr → Bool
  | .bvar _ => true
  | e => e.isValue

private theorem quoteEnv_shape (ρ : RuntimeEnv) (i : Nat) : valueOrIndex (quoteEnv ρ i) = true := by
  rw [quoteEnv_lookup]
  cases ρ[i]? with
  | none => rfl
  | some v => cases v <;> rfl

private theorem quoteEnv_ne {ρ : RuntimeEnv} {i : Nat} {e : Expr}
    (compound : valueOrIndex e = false) (equal : quoteEnv ρ i = e) : False :=
  Bool.false_ne_true (compound.symm.trans (equal ▸ quoteEnv_shape ρ i))

private theorem quote_int {v : RuntimeValue} {n : Int} (h : quote v = .int n) : v = .int n := by
  cases v <;> simp_all [quote, Expr.recClosure]

private theorem quote_bool {v : RuntimeValue} {b : Bool} (h : quote v = .bool b) : v = .bool b := by
  cases v <;> simp_all [quote, Expr.recClosure]

private theorem quote_skip {v : RuntimeValue} (h : quote v = .skip) : v = .unit := by
  cases v <;> simp_all [quote, Expr.recClosure]

/-- Pull an evaluation back through the substitution represented by a
lexical environment. -/
private def Realizable (e : Expr) (s : Store) (result : Config) : Prop :=
  ∀ (ρ : RuntimeEnv) (source : Expr), source.subst (quoteEnv ρ) = e →
    ∃ v, Returns ρ source s v result.store ∧ quote v = result.expr

private theorem realizes_value {e : Expr} {s : Store} (value : IsValue e) :
    Realizable e s ⟨e, s⟩ := by
  intro ρ source equal
  subst e
  cases source <;> simp only [Expr.subst] at value ⊢
  case int n => exact ⟨_, .int n, rfl⟩
  case bool b => exact ⟨_, .bool b, rfl⟩
  case skip => exact ⟨_, .skip, rfl⟩
  case lam => exact ⟨_, .lam, rfl⟩
  case bvar i =>
    rw [quoteEnv_lookup] at value ⊢
    cases lookup : ρ[i]? with
    | none =>
      rw [lookup] at value
      cases value
    | some v =>
      exact ⟨v, .var lookup, rfl⟩
  all_goals cases value

private def enterRec : Expr → Expr
  | .letRecFun A B fn body => body.beta (Expr.recClosure A B fn)
  | e => e

/-- The second induction conclusion makes the body of a renewed recursive
binding available to the application case. -/
private theorem SubstitutionReturn.complete {e : Expr} {s : Store} {result : Config}
    (run : SubstitutionReturn e s result) :
    Realizable e s result ∧ Realizable (enterRec e) s result := by
  induction run with
  | value value =>
    exact ⟨realizes_value value, by cases value <;> exact realizes_value (by constructor)⟩
  | add _ _ ihLeft ihRight =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    all_goals cases equal
    obtain ⟨_, left, first⟩ := ihLeft.1 ρ _ rfl
    obtain ⟨_, right, second⟩ := ihRight.1 ρ _ rfl
    cases quote_int first
    cases quote_int second
    exact ⟨_, .add left right, rfl⟩
  | ge _ _ ihLeft ihRight =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    all_goals cases equal
    obtain ⟨_, left, first⟩ := ihLeft.1 ρ _ rfl
    obtain ⟨_, right, second⟩ := ihRight.1 ρ _ rfl
    cases quote_int first
    cases quote_int second
    exact ⟨_, .ge left right, rfl⟩
  | deref lookup =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    all_goals cases equal
    exact ⟨_, .deref lookup, rfl⟩
  | assign _ present ih =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    all_goals cases equal
    obtain ⟨_, rhs, observed⟩ := ih.1 ρ _ rfl
    cases quote_int observed
    exact ⟨_, .assign rhs present, rfl⟩
  | seq _ _ ihLeft ihRight =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    all_goals cases equal
    obtain ⟨_, left, first⟩ := ihLeft.1 ρ _ rfl
    obtain ⟨_, right, second⟩ := ihRight.1 ρ _ rfl
    cases quote_skip first
    exact ⟨_, .seq left right, second⟩
  | ifTrue _ _ ihTest ihYes =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    all_goals cases equal
    obtain ⟨_, test, first⟩ := ihTest.1 ρ _ rfl
    obtain ⟨_, yes, second⟩ := ihYes.1 ρ _ rfl
    cases quote_bool first
    exact ⟨_, .ifTrue test yes, second⟩
  | ifFalse _ _ ihTest ihNo =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    all_goals cases equal
    obtain ⟨_, test, first⟩ := ihTest.1 ρ _ rfl
    obtain ⟨_, no, second⟩ := ihNo.1 ρ _ rfl
    cases quote_bool first
    exact ⟨_, .ifFalse test no, second⟩
  | whileFalse _ ihTest =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    all_goals cases equal
    obtain ⟨_, test, observed⟩ := ihTest.1 ρ _ rfl
    cases quote_bool observed
    exact ⟨_, .whileFalse test, rfl⟩
  | whileTrue _ _ _ ihTest ihBody ihRest =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    all_goals cases equal
    obtain ⟨_, test, first⟩ := ihTest.1 ρ _ rfl
    obtain ⟨_, body, second⟩ := ihBody.1 ρ _ rfl
    obtain ⟨_, rest, third⟩ := ihRest.1 ρ (.loop _ _) rfl
    cases quote_bool first
    cases quote_skip second
    cases quote_skip third
    exact ⟨_, .whileTrue test body rest, rfl⟩
  | @app _ _ fnBody argument A _ _ _ _ _ _ _ ihFn ihArg ihBody =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    all_goals cases equal
    obtain ⟨function, fn, fnQuote⟩ := ihFn.1 ρ _ rfl
    obtain ⟨argValue, arg, argQuote⟩ := ihArg.1 ρ _ rfl
    cases function <;> simp only [quote, Expr.recClosure] at fnQuote
    case closure capturedType capturedBody saved =>
      cases fnQuote
      have instantiation : capturedBody.subst (quoteEnv (argValue :: saved)) =
          (capturedBody.subst (Expr.liftSubst (quoteEnv saved))).beta argument := by
        rw [beta_after_subst, quoteEnv_cons, argQuote]
      obtain ⟨_, returned, observed⟩ := ihBody.1 _ _ instantiation
      exact ⟨_, .app fn arg returned, observed⟩
    case recursive capturedType codomain capturedBody saved =>
      cases fnQuote
      let self := RuntimeValue.recursive A codomain capturedBody saved
      have instantiation : capturedBody.subst (quoteEnv (argValue :: self :: saved)) =
          enterRec ((Expr.letRecFun A codomain
            ((capturedBody.subst (Expr.liftSubst (Expr.liftSubst (quoteEnv saved)))).rename
              (DeBruijn.liftN 2 Nat.succ))
            ((capturedBody.subst (Expr.liftSubst (Expr.liftSubst (quoteEnv saved)))).rename
              swapFirstTwo)).beta argument) := by
        rw [recClosure_body_beta]
        simp only [enterRec, recClosure_enter, quoteEnv_cons, argQuote, self, quote]
      obtain ⟨_, returned, observed⟩ := ihBody.2 _ _ instantiation
      exact ⟨_, .appRec fn arg returned, observed⟩
    all_goals contradiction
  | @letE _ _ argument _ _ _ _ _ _ ihRhs ihBody =>
    suffices h : Realizable _ _ _ from ⟨h, h⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    case letE _ _ body =>
      cases equal
      obtain ⟨argValue, rhsRun, quoted⟩ := ihRhs.1 ρ _ rfl
      have instantiation : body.subst (quoteEnv (argValue :: ρ)) =
          (body.subst (Expr.liftSubst (quoteEnv ρ))).beta argument := by
        rw [beta_after_subst, quoteEnv_cons, quoted]
      obtain ⟨_, returned, observed⟩ := ihBody.1 _ _ instantiation
      exact ⟨_, .letE rhsRun returned, observed⟩
    all_goals cases equal
  | @letRec _ _ A B _ _ _ ih =>
    refine ⟨?_, ih.1⟩
    intro ρ source equal
    cases source <;> simp only [Expr.subst] at equal
    case bvar => exact (quoteEnv_ne rfl equal).elim
    case letRecFun _ _ fn body =>
      cases equal
      let self := RuntimeValue.recursive A B fn ρ
      have instantiation : body.subst (quoteEnv (self :: ρ)) =
          (body.subst (Expr.liftSubst (quoteEnv ρ))).beta
            (Expr.recClosure A B (fn.subst (Expr.liftSubst (Expr.liftSubst (quoteEnv ρ))))) := by
        rw [beta_after_subst, quoteEnv_cons]
        rfl
      obtain ⟨_, returned, observed⟩ := ih.1 _ _ instantiation
      exact ⟨_, .letRec returned, observed⟩
    all_goals cases equal

/-- A finite observation includes the quoted value and the full final store. -/
def Observes (ρ : RuntimeEnv) (e : Expr) (s : Store) (result : Config) : Prop :=
  ∃ v, Returns ρ e s v result.store ∧ quote v = result.expr

/-- Interpreting a lexical environment agrees with the existing L2 relation
after substituting its quoted values. -/
theorem adequate_env (ρ : RuntimeEnv) (e : Expr) (s : Store) (result : Config) :
    Observes ρ e s result ↔
      Steps ⟨e.subst (quoteEnv ρ), s⟩ result ∧ IsValue result.expr := by
  rw [← substitutionReturn_iff]
  constructor
  · rintro ⟨v, run, observed⟩
    cases result
    cases observed
    exact run.sound
  · intro run
    exact run.complete.1 ρ e rfl

theorem adequate (e : Expr) (s : Store) (result : Config) :
    Observes [] e s result ↔ Steps ⟨e, s⟩ result ∧ IsValue result.expr := by
  have empty : quoteEnv [] = Expr.bvar := by funext i; rfl
  simpa only [empty, Expr.subst_id] using adequate_env [] e s result

end Silmaril.Courses.Cambridge.L2.RelationalDenotation
