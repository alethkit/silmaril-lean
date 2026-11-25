module

public import Silmaril.Courses.Cambridge.L3.Denotation

/-! # Bounded call depth for Cambridge L3 denotations

The lexical model interprets a value as a quote with its captured
bindings. The additional layer runs a strict let prefix and a tail
application with lexical operands. On invoking a quote, it interprets
the body at the previous call depth with the argument in slot zero
and the store left by the argument calculation.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Denotation.CallDepth

/-- Enter a quoted closure with its new argument. The quote already
contains its captured lexical bindings. -/
def applyBody (interpretBody : Environment → Expr → Computation Value)
    (function argument : Value) : Computation Value :=
  match function.val with
  | .lam _ body => interpretBody (Environment.empty.extend argument) body
  | _ => fail

/-- A tail application can follow strict lets whose initializers are
lexical. Each operand is interpreted before invoking the resulting closure. -/
def denoteLayer (interpretBody : Environment → Expr → Computation Value)
    (env : Environment) : Expr → Computation Value
  | .letE _ value body =>
      Denotation.denoteWith env value >>= fun result =>
        denoteLayer interpretBody (env.extend result) body
  | .app fn arg =>
      Denotation.denoteWith env fn >>= fun function =>
        Denotation.denoteWith env arg >>= applyBody interpretBody function
  | e => Denotation.denoteWith env e
termination_by structural e => e

/-- The index bounds nested invocations. Lexical computations retain their
ordinary finite-return semantics at every layer. -/
def denoteWith : Nat → Environment → Expr → Computation Value
  | 0 => Denotation.denoteWith
  | depth + 1 => denoteLayer (denoteWith depth)

def denote (depth : Nat) (e : Expr) : Computation Value :=
  denoteWith depth Environment.empty e

/-- The index allows one more invocation at each application. Check the
callee for each pair of operand returns, in the environment and store with
which it is actually entered. Every possible return of a let initializer
must also admit the continuation. -/
inductive Admitted : Nat → Environment → Store → Expr → Prop where
  | lexical {depth : Nat} {env : Environment} {s : Store} {e : Expr}
      (fragment : Fragment e) : Admitted depth env s e
  | letE {depth : Nat} {env : Environment} {s : Store} {A : Ty} {value body : Expr}
      (bound : Fragment value)
      (bodyAdmitted : ∀ {v t}, Returns (Denotation.denoteWith env value) s v t →
        Admitted (depth + 1) (env.extend v) t body) :
      Admitted (depth + 1) env s (.letE A value body)
  | app {depth : Nat} {env : Environment} {s : Store} {fn arg : Expr}
      (function : Fragment fn) (argument : Fragment arg)
      (bodyAdmitted : ∀ {A body middle a afterArgument},
        Returns (Denotation.denoteWith env fn) s ⟨.lam A body, .lam A body⟩ middle →
        Returns (Denotation.denoteWith env arg) middle a afterArgument →
        Admitted depth (Environment.empty.extend a) afterArgument body) :
      Admitted (depth + 1) env s (.app fn arg)

private theorem denoteLayer_of_fragment {e : Expr} (fragment : Fragment e)
    (interpretBody : Environment → Expr → Computation Value) (env : Environment) :
    denoteLayer interpretBody env e = Denotation.denoteWith env e := by
  induction fragment generalizing env with
  | value ready => cases ready <;> rfl
  | letE _ _ _ ih =>
      simp only [denoteLayer, Denotation.denoteWith, ih]
  | bvar | matchSum | binary | cond | seq | loop | pair | fst | snd | inl | inr |
    record | project | ref | deref | assign => rfl

theorem denoteWith_of_fragment {e : Expr} (fragment : Fragment e)
    (depth : Nat) (env : Environment) :
    denoteWith depth env e = Denotation.denoteWith env e := by
  cases depth with
  | zero => rfl
  | succ depth => exact denoteLayer_of_fragment fragment (denoteWith depth) env

private theorem frame (plug : Expr → Expr)
    (lift : ∀ {e e' : Expr} {s s' : Store}, Step ⟨e, s⟩ ⟨e', s'⟩ →
      Step ⟨plug e, s⟩ ⟨plug e', s'⟩)
    {e e' : Expr} {s s' : Store} (trace : Steps ⟨e, s⟩ ⟨e', s'⟩) :
    Steps ⟨plug e, s⟩ ⟨plug e', s'⟩ :=
  trace.lift (fun c => (⟨plug c.expr, c.store⟩ : Config)) (fun ⟨_, _⟩ ⟨_, _⟩ step => lift step)

private theorem value_no_step {e : Expr} (value : IsValue e) {s : Store} {t : Config} :
    ¬ Step ⟨e, s⟩ t := by
  induction value generalizing s t <;> intro step <;> cases step
  all_goals solve_by_elim

private theorem value_steps {e : Expr} (value : IsValue e) {s : Store} {t : Config}
    (trace : Steps ⟨e, s⟩ t) : (⟨e, s⟩ : Config) = t := by
  rcases trace.cases_head with same | ⟨_, step, _⟩
  · exact same
  · exact (value_no_step value step).elim

private theorem app_iff {fn arg : Expr} {s : Store} {target : Config} (ready : IsValue target.expr) :
    Steps ⟨.app fn arg, s⟩ target ↔
      ∃ (A : Ty) (body : Expr) (argument : Value) (middle afterArgument : Store),
        Steps ⟨fn, s⟩ ⟨.lam A body, middle⟩ ∧
        Steps ⟨arg, middle⟩ ⟨argument.val, afterArgument⟩ ∧
        Steps ⟨body.beta argument.val, afterArgument⟩ target := by
  constructor
  · intro trace
    have inv {source : Config} (trace : Steps source target) :
        ∀ (fn arg : Expr) (s : Store), source = ⟨.app fn arg, s⟩ →
          ∃ (A : Ty) (body : Expr) (argument : Value) (middle afterArgument : Store),
            Steps ⟨fn, s⟩ ⟨.lam A body, middle⟩ ∧
            Steps ⟨arg, middle⟩ ⟨argument.val, afterArgument⟩ ∧
            Steps ⟨body.beta argument.val, afterArgument⟩ target := by
      induction trace using Relation.ReflTransGen.head_induction_on with
      | refl =>
          intro fn arg store equal
          rw [equal] at ready
          cases ready
      | @head source next step tail ih =>
          intro fn arg store equal
          subst source
          cases step with
          | appLeft inner =>
              obtain ⟨A, body, argument, middle, afterArgument, f, a, b⟩ := ih _ _ _ rfl
              exact ⟨A, body, argument, middle, afterArgument, f.head inner, a, b⟩
          | appRight functionReady inner =>
              obtain ⟨A, body, argument, middle, afterArgument, f, a, b⟩ := ih _ _ _ rfl
              have equal := value_steps functionReady f
              cases equal
              exact ⟨A, body, argument, store, afterArgument, .refl, a.head inner, b⟩
          | appFun argumentReady =>
              exact ⟨_, _, ⟨_, argumentReady⟩, store, store, .refl, .refl, tail⟩
    exact inv trace fn arg s rfl
  · rintro ⟨A, body, argument, middle, afterArgument, evaluatedFn, evaluatedArg, called⟩
    have f := frame (fun e => .app e arg) Step.appLeft evaluatedFn
    have a := frame (Expr.app (.lam A body)) (Step.appRight (.lam A body)) evaluatedArg
    exact (f.trans a).trans (called.head (.appFun argument.property))

private theorem let_iff {A : Ty} {value body : Expr} {s : Store} {target : Config}
    (ready : IsValue target.expr) :
    Steps ⟨.letE A value body, s⟩ target ↔
      ∃ (bound : Value) (middle : Store), Steps ⟨value, s⟩ ⟨bound.val, middle⟩ ∧
        Steps ⟨body.beta bound.val, middle⟩ target := by
  constructor
  · intro trace
    have inv {source : Config} (trace : Steps source target) :
        ∀ (value : Expr) (s : Store), source = ⟨.letE A value body, s⟩ →
          ∃ (bound : Value) (middle : Store), Steps ⟨value, s⟩ ⟨bound.val, middle⟩ ∧
            Steps ⟨body.beta bound.val, middle⟩ target := by
      induction trace using Relation.ReflTransGen.head_induction_on with
      | refl =>
          intro value store equal
          rw [equal] at ready
          cases ready
      | @head source next step tail ih =>
          intro value store equal
          subst source
          cases step with
          | letStep inner =>
              obtain ⟨bound, middle, v, b⟩ := ih _ _ rfl
              exact ⟨bound, middle, v.head inner, b⟩
          | letValue valueReady =>
              exact ⟨⟨value, valueReady⟩, store, .refl, tail⟩
    exact inv trace value s rfl
  · rintro ⟨bound, _, evaluated, runBody⟩
    exact (frame (fun e => .letE A e body) Step.letStep evaluated).trans
      (runBody.head (.letValue bound.property))

private theorem beta_after_capture (body : Expr) (value : Value) (env : Environment) :
    (body.subst (Expr.liftSubst env.substitution)).beta value.val =
      body.subst (env.extend value).substitution := by
  rw [Expr.beta, Expr.subst_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      rw [Expr.liftSubst, Expr.subst_rename]
      exact Expr.subst_id _

private theorem instantiate_argument (body : Expr) (argument : Value) :
    body.subst (Environment.empty.extend argument).substitution = body.beta argument.val := by
  unfold Expr.beta
  congr 1
  funext i
  cases i <;> rfl

/-- Exact finite may adequacy at an admitted call depth. The result and
the whole final store agree with the original L3 rules. The index bounds
callee nesting and need not bound the length of the source trace. -/
theorem adequateWith {depth : Nat} {env : Environment} {s t : Store} {e : Expr} {result : Value}
    (admitted : Admitted depth env s e) :
    Returns (denoteWith depth env e) s result t ↔
      Steps ⟨e.subst env.substitution, s⟩ ⟨result.val, t⟩ := by
  induction admitted with
  | lexical fragment =>
      rw [denoteWith_of_fragment fragment]
      exact Denotation.adequateWith _ fragment
  | @letE depth env s A value body bound _ ih =>
      simp only [denoteWith, denoteLayer, Expr.subst, returns_bind,
        let_iff (target := ⟨result.val, t⟩) result.property, beta_after_capture]
      constructor
      · rintro ⟨v, middle, evaluated, continued⟩
        exact ⟨v, middle, (Denotation.adequateWith env bound).mp evaluated,
          (ih evaluated).mp continued⟩
      · rintro ⟨v, middle, evaluated, continued⟩
        have returned := (Denotation.adequateWith env bound).mpr evaluated
        exact ⟨v, middle, returned, (ih returned).mpr continued⟩
  | @app depth env s fn arg function argument _ ih =>
      simp only [denoteWith, denoteLayer, Expr.subst, returns_bind,
        app_iff (target := ⟨result.val, t⟩) result.property]
      constructor
      · rintro ⟨f, middle, evaluatedFn, a, afterArgument, evaluatedArg, invoked⟩
        rcases f with ⟨_, ready⟩
        cases ready <;> try contradiction
        case lam A body =>
          have called := (ih evaluatedFn evaluatedArg).mp invoked
          rw [instantiate_argument] at called
          exact ⟨A, body, a, middle, afterArgument,
            (Denotation.adequateWith env function).mp evaluatedFn,
            (Denotation.adequateWith env argument).mp evaluatedArg, called⟩
      · rintro ⟨A, body, a, middle, afterArgument, evaluatedFn, evaluatedArg, invoked⟩
        have returnedFn := (Denotation.adequateWith env function
          (v := ⟨.lam A body, .lam A body⟩)).mpr evaluatedFn
        have returnedArg := (Denotation.adequateWith env argument).mpr evaluatedArg
        rw [← instantiate_argument] at invoked
        exact ⟨⟨.lam A body, .lam A body⟩, middle, returnedFn, a, afterArgument, returnedArg,
          (ih returnedFn returnedArg).mpr invoked⟩

theorem adequate {depth : Nat} {s t : Store} {e : Expr} {result : Value}
    (admitted : Admitted depth Environment.empty s e) :
    Returns (denote depth e) s result t ↔ Steps ⟨e, s⟩ ⟨result.val, t⟩ := by
  simpa only [denote, show Environment.empty.substitution = Expr.bvar from rfl, Expr.subst_id] using
    (adequateWith admitted (result := result) (t := t))

theorem typed_return {depth : Nat} {Θ : LocTypes} {T : Ty} {e : Expr} {s t : Store} {result : Value}
    (admitted : Admitted depth Environment.empty s e) (typed : HasType Θ .empty e T)
    (store : StoreTyped Θ s) (returned : Returns (denote depth e) s result t) :
    ∃ Θ', Θ.Extends Θ' ∧ HasType Θ' .empty result.val T ∧ StoreTyped Θ' t :=
  preservation_steps ((adequate admitted).mp returned) typed store

end Silmaril.Courses.Cambridge.L3.Denotation.CallDepth
