module

public import Silmaril.Courses.Cambridge.L3.Denotation

/-! # A single dynamic L3 application in the state-and-powerset model

The function and argument use the lexical denotation. The function's quoted
body already contains its captured bindings. Calling it supplies the new
argument in an otherwise empty environment and runs the body in the store
left by the argument computation. A strict lexical let may prefix the call.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Denotation.SingleCall

def applyClosure (function argument : Value) : Computation Value :=
  match function.val with
  | .lam _ body => Denotation.denoteWith (Environment.empty.extend argument) body
  | _ => fail

/-- Interpret lexical prefixes and one tail application. At the call site,
both operands and the selected function body use the lexical model. -/
def denoteWith (env : Environment) : Expr → Computation Value
  | .letE _ value body =>
      Denotation.denoteWith env value >>= fun result => denoteWith (env.extend result) body
  | .app fn arg =>
      Denotation.denoteWith env fn >>= fun function =>
        Denotation.denoteWith env arg >>= applyClosure function
  | e => Denotation.denoteWith env e
termination_by structural e => e

def denote (e : Expr) : Computation Value := denoteWith Environment.empty e

/-- The single-call grammar admits lexical terms, strict let prefixes, and
a tail call with lexical operands. Every lambda returned by the function
operand must have a lexical body. Prefix lets check their body on every
possible binding return, with that branch's environment and store. -/
inductive Admitted : Environment → Store → Expr → Prop where
  | lexical {env s e} (fragment : Fragment e) : Admitted env s e
  | letE {env s A value body} (bound : Fragment value)
      (bodyAdmitted : ∀ {v t}, Returns (Denotation.denoteWith env value) s v t →
        Admitted (env.extend v) t body) :
      Admitted env s (.letE A value body)
  | app {env s fn arg} (function : Fragment fn) (argument : Fragment arg)
      (bodyAdmitted : ∀ {A body t},
        Returns (Denotation.denoteWith env fn) s ⟨.lam A body, .lam A body⟩ t →
          Fragment body) :
      Admitted env s (.app fn arg)

theorem denoteWith_of_fragment {e : Expr} (fragment : Fragment e) (env : Environment) :
    denoteWith env e = Denotation.denoteWith env e := by
  induction fragment generalizing env with
  | value ready => cases ready <;> rfl
  | letE _ _ _ ih =>
      simp only [denoteWith, Denotation.denoteWith, ih]
  | bvar | matchSum | binary | cond | seq | loop | pair | fst | snd | inl | inr |
    record | project | ref | deref | assign => rfl

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

private theorem applied_iff {A : Ty} {body : Expr} {argument result : Value} {s t : Store}
    (admitted : Fragment body) :
    Returns (applyClosure ⟨.lam A body, .lam A body⟩ argument) s result t ↔
      Steps ⟨body.beta argument.val, s⟩ ⟨result.val, t⟩ := by
  have instantiated : body.subst (Environment.empty.extend argument).substitution =
      body.beta argument.val := by
    unfold Expr.beta
    congr 1
    funext i
    cases i <;> rfl
  simpa only [applyClosure, instantiated] using
    (Denotation.adequateWith (Environment.empty.extend argument) admitted (s := s) (t := t) (v := result))

/-- Exact may adequacy for a single call with strict lexical prefixes. A
return includes its complete value expression and the final store. -/
theorem adequateWith {env : Environment} {s t : Store} {e : Expr} {result : Value}
    (admitted : Admitted env s e) :
    Returns (denoteWith env e) s result t ↔
      Steps ⟨e.subst env.substitution, s⟩ ⟨result.val, t⟩ := by
  induction admitted with
  | lexical fragment =>
      rw [denoteWith_of_fragment fragment]
      exact Denotation.adequateWith _ fragment
  | @letE env s A value body bound _ ih =>
      simp only [denoteWith, Expr.subst, returns_bind,
        let_iff (target := ⟨result.val, t⟩) result.property, beta_after_capture]
      constructor
      · rintro ⟨v, middle, evaluated, continued⟩
        exact ⟨v, middle, (Denotation.adequateWith env bound).mp evaluated,
          (ih evaluated).mp continued⟩
      · rintro ⟨v, middle, evaluated, continued⟩
        have returned := (Denotation.adequateWith env bound).mpr evaluated
        exact ⟨v, middle, returned, (ih returned).mpr continued⟩
  | @app env s fn arg function argument bodies =>
      simp only [denoteWith, Expr.subst, returns_bind, app_iff (target := ⟨result.val, t⟩) result.property]
      constructor
      · rintro ⟨f, middle, evaluatedFn, a, afterArgument, evaluatedArg, invoked⟩
        rcases f with ⟨_, ready⟩
        cases ready <;> try contradiction
        case lam A body =>
          exact ⟨A, body, a, middle, afterArgument,
            (Denotation.adequateWith env function).mp evaluatedFn,
            (Denotation.adequateWith env argument).mp evaluatedArg,
            (applied_iff (bodies evaluatedFn)).mp invoked⟩
      · rintro ⟨A, body, a, middle, afterArgument, evaluatedFn, evaluatedArg, invoked⟩
        have returnedFn := (Denotation.adequateWith env function
          (v := ⟨.lam A body, .lam A body⟩)).mpr evaluatedFn
        exact ⟨⟨.lam A body, .lam A body⟩, middle, returnedFn,
          a, afterArgument, (Denotation.adequateWith env argument).mpr evaluatedArg,
          (applied_iff (bodies returnedFn)).mpr invoked⟩

theorem adequate {s t : Store} {e : Expr} {result : Value}
    (admitted : Admitted Environment.empty s e) :
    Returns (denote e) s result t ↔ Steps ⟨e, s⟩ ⟨result.val, t⟩ := by
  simpa only [denote, show Environment.empty.substitution = Expr.bvar from rfl, Expr.subst_id] using
    (adequateWith admitted (result := result) (t := t))

theorem typed_return {Θ : LocTypes} {T : Ty} {e : Expr} {s t : Store} {result : Value}
    (admitted : Admitted Environment.empty s e) (typed : HasType Θ .empty e T)
    (store : StoreTyped Θ s) (returned : Returns (denote e) s result t) :
    ∃ Θ', Θ.Extends Θ' ∧ HasType Θ' .empty result.val T ∧ StoreTyped Θ' t :=
  preservation_steps ((adequate admitted).mp returned) typed store

end Silmaril.Courses.Cambridge.L3.Denotation.SingleCall
