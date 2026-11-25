module

public import Silmaril.Courses.Cambridge.L3.Denotation.CallDepth

/-! # A single dynamic L3 application in the state-and-powerset model

The function and argument use the lexical denotation. The function's quoted
body already contains its captured bindings. Calling it supplies the new
argument in an otherwise empty environment and runs the body in the store
left by the argument computation. A strict lexical let may prefix the call.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Denotation.SingleCall

def applyClosure (function argument : Value) : Computation Value :=
  CallDepth.applyBody Denotation.denoteWith function argument

/-- Interpret lexical prefixes and one tail application. At the call site,
both operands and the selected function body use the lexical model. -/
def denoteWith (env : Environment) (e : Expr) : Computation Value :=
  CallDepth.denoteWith 1 env e

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
    denoteWith env e = Denotation.denoteWith env e :=
  CallDepth.denoteWith_of_fragment fragment 1 env

theorem Admitted.toCallDepth {env : Environment} {s : Store} {e : Expr} (admitted : Admitted env s e) :
    CallDepth.Admitted 1 env s e := by
  induction admitted with
  | lexical fragment => exact .lexical fragment
  | letE bound _ ih => exact .letE bound (fun returned => ih returned)
  | app function argument bodies =>
      exact .app function argument (fun returned _ => .lexical (bodies returned))

/-- Exact may adequacy for a single call with strict lexical prefixes. A
return includes its complete value expression and the final store. -/
theorem adequateWith {env : Environment} {s t : Store} {e : Expr} {result : Value}
    (admitted : Admitted env s e) :
    Returns (denoteWith env e) s result t ↔
      Steps ⟨e.subst env.substitution, s⟩ ⟨result.val, t⟩ :=
  CallDepth.adequateWith admitted.toCallDepth

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
