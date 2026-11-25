module

public import Silmaril.Courses.Cambridge.L3.Typing
public import Silmaril.Courses.Cambridge.L3.Reduction

/-! # Exercise 30: payload-free exceptions

Design for §5.6, p. 82 of the 12 February 2026 notes. The parameter
`Name` supplies exception tags (for example, a type of declared names).
The exercise language has CBV functions and recursion and embeds closed L3
computations over the shared store. Functions with exception-aware bodies
have a local function type. Each handler catches one tag, and its recovery
expression runs after that handler has been removed.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Exercises.Exceptions

inductive Ty where
  | core (type : L3.Ty)
  | arr (domain codomain : Ty)

inductive Expr (Name : Type) where
  | core (code : L3.Expr)
  | var (index : Nat)
  | lam (domain : Ty) (body : Expr Name)
  | app (fn arg : Expr Name)
  | letE (type : Ty) (rhs body : Expr Name)
  | cond (test yes no : Expr Name)
  | letRec (domain codomain : Ty) (definition body : Expr Name)
  | raise (name : Name)
  | handle (body : Expr Name) (name : Name) (recovery : Expr Name)
  /-- Internal recursive closure. Its body binds the parameter then the function. -/
  | recClosure (domain codomain : Ty) (body : Expr Name)

variable {Name : Type}

def Expr.rename (ρ : Nat → Nat) : Expr Name → Expr Name
  | .core e => .core e
  | .var i => .var (ρ i)
  | .lam A body => .lam A (body.rename (DeBruijn.lift ρ))
  | .app f x => .app (f.rename ρ) (x.rename ρ)
  | .letE A rhs body => .letE A (rhs.rename ρ) (body.rename (DeBruijn.lift ρ))
  | .cond test yes no => .cond (test.rename ρ) (yes.rename ρ) (no.rename ρ)
  | .letRec A B fn body =>
    .letRec A B (fn.rename (DeBruijn.liftN 2 ρ)) (body.rename (DeBruijn.lift ρ))
  | .raise name => .raise name
  | .handle body name recovery => .handle (body.rename ρ) name (recovery.rename ρ)
  | .recClosure A B body => .recClosure A B (body.rename (DeBruijn.liftN 2 ρ))

def Expr.extend (e : Expr Name) (σ : Nat → Expr Name) : Nat → Expr Name
  | 0 => e
  | i + 1 => σ i

def Expr.liftSubst (σ : Nat → Expr Name) : Nat → Expr Name :=
  extend (.var 0) (fun i => (σ i).rename Nat.succ)

def Expr.subst (σ : Nat → Expr Name) : Expr Name → Expr Name
  | .core e => .core e
  | .var i => σ i
  | .lam A body => .lam A (body.subst (liftSubst σ))
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .letE A rhs body => .letE A (rhs.subst σ) (body.subst (liftSubst σ))
  | .cond test yes no => .cond (test.subst σ) (yes.subst σ) (no.subst σ)
  | .letRec A B fn body => .letRec A B (fn.subst (liftSubst (liftSubst σ))) (body.subst (liftSubst σ))
  | .raise name => .raise name
  | .handle body name recovery => .handle (body.subst σ) name (recovery.subst σ)
  | .recClosure A B body => .recClosure A B (body.subst (liftSubst (liftSubst σ)))

def Expr.beta (body argument : Expr Name) : Expr Name := body.subst (extend argument Expr.var)

def Expr.recBeta (A B : Ty) (body argument : Expr Name) : Expr Name :=
  body.subst (extend argument (extend (.recClosure A B body) Expr.var))

inductive HasType (Θ : LocTypes) : List Ty → Expr Name → Ty → Prop where
  | core {Γ : List Ty} {e : L3.Expr} {A : L3.Ty} :
    L3.HasType Θ .empty e A → HasType Θ Γ (.core e) (.core A)
  | var {Γ : List Ty} {i : Nat} {A : Ty} :
    Γ[i]? = some A → HasType Θ Γ (.var i) A
  | lam {Γ : List Ty} {A B : Ty} {body : Expr Name} :
    HasType Θ (A :: Γ) body B → HasType Θ Γ (.lam A body) (.arr A B)
  | app {Γ : List Ty} {A B : Ty} {f x : Expr Name} :
    HasType Θ Γ f (.arr A B) → HasType Θ Γ x A → HasType Θ Γ (.app f x) B
  | letE {Γ : List Ty} {A B : Ty} {rhs body : Expr Name} :
    HasType Θ Γ rhs A → HasType Θ (A :: Γ) body B → HasType Θ Γ (.letE A rhs body) B
  | cond {Γ : List Ty} {A : Ty} {test yes no : Expr Name} :
    HasType Θ Γ test (.core .bool) → HasType Θ Γ yes A → HasType Θ Γ no A →
    HasType Θ Γ (.cond test yes no) A
  | letRec {Γ : List Ty} {A B T : Ty} {fn body : Expr Name} :
    HasType Θ (A :: .arr A B :: Γ) fn B → HasType Θ (.arr A B :: Γ) body T →
    HasType Θ Γ (.letRec A B fn body) T
  | raise {Γ : List Ty} {T : Ty} (name : Name) : HasType Θ Γ (.raise name) T
  | handle {Γ : List Ty} {T : Ty} {body recovery : Expr Name} {name : Name} :
    HasType Θ Γ body T → HasType Θ Γ recovery T → HasType Θ Γ (.handle body name recovery) T
  | recClosure {Γ : List Ty} {A B : Ty} {fn : Expr Name} :
    HasType Θ (A :: .arr A B :: Γ) fn B → HasType Θ Γ (.recClosure A B fn) (.arr A B)

inductive IsValue : Expr Name → Prop where
  | core {e : L3.Expr} : L3.IsValue e → IsValue (.core e)
  | lam (A : Ty) (body : Expr Name) : IsValue (.lam A body)
  | recClosure (A B : Ty) (body : Expr Name) : IsValue (.recClosure A B body)

/-- Handler-free evaluation frames expose the active position in CBV order. -/
inductive Frame (Name : Type) where
  | appFn (arg : Expr Name)
  | appArg (fn : Expr Name) (ready : IsValue fn)
  | letRhs (type : Ty) (body : Expr Name)
  | condTest (yes no : Expr Name)

def Frame.plug : Frame Name → Expr Name → Expr Name
  | .appFn arg, e => .app e arg
  | .appArg fn _, e => .app fn e
  | .letRhs A body, e => .letE A e body
  | .condTest yes no, e => .cond e yes no

structure Config (Name : Type) where
  expr : Expr Name
  store : Store

inductive Step : Config Name → Config Name → Prop where
  | core {e e' : L3.Expr} {s s' : Store} :
    L3.Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.core e, s⟩ ⟨.core e', s'⟩
  | frame (frame : Frame Name) {e e' : Expr Name} {s s' : Store} :
    Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨frame.plug e, s⟩ ⟨frame.plug e', s'⟩
  | unwind (frame : Frame Name) (name : Name) (s : Store) :
    Step ⟨frame.plug (.raise name), s⟩ ⟨.raise name, s⟩
  | app {A : Ty} {body argument : Expr Name} {s : Store} : IsValue argument →
    Step ⟨.app (.lam A body) argument, s⟩ ⟨body.beta argument, s⟩
  | appRec {A B : Ty} {body argument : Expr Name} {s : Store} : IsValue argument →
    Step ⟨.app (.recClosure A B body) argument, s⟩ ⟨body.recBeta A B argument, s⟩
  | letE {A : Ty} {rhs body : Expr Name} {s : Store} : IsValue rhs →
    Step ⟨.letE A rhs body, s⟩ ⟨body.beta rhs, s⟩
  | letRec {A B : Ty} {fn body : Expr Name} {s : Store} :
    Step ⟨.letRec A B fn body, s⟩ ⟨body.beta (.recClosure A B fn), s⟩
  | ifTrue {yes no : Expr Name} {s : Store} :
    Step ⟨.cond (.core (.bool true)) yes no, s⟩ ⟨yes, s⟩
  | ifFalse {yes no : Expr Name} {s : Store} :
    Step ⟨.cond (.core (.bool false)) yes no, s⟩ ⟨no, s⟩
  | handleStep {body body' recovery : Expr Name} {name : Name} {s s' : Store} :
    Step ⟨body, s⟩ ⟨body', s'⟩ →
    Step ⟨.handle body name recovery, s⟩ ⟨.handle body' name recovery, s'⟩
  | handleValue {e recovery : Expr Name} {name : Name} {s : Store} : IsValue e →
    Step ⟨.handle e name recovery, s⟩ ⟨e, s⟩
  | catchRaise {name : Name} {recovery : Expr Name} {s : Store} :
    Step ⟨.handle (.raise name) name recovery, s⟩ ⟨recovery, s⟩
  | miss {name other : Name} {recovery : Expr Name} {s : Store} : name ≠ other →
    Step ⟨.handle (.raise name) other recovery, s⟩ ⟨.raise name, s⟩

abbrev Steps (c d : Config Name) := Relation.ReflTransGen Step c d

theorem raise_terminal (name : Name) (s : Store) (target : Config Name) :
    ¬ Step ⟨.raise name, s⟩ target := by
  intro step
  generalize eq : (⟨.raise name, s⟩ : Config Name) = before at step
  cases step
  case frame frame _ _ _ _ _ => cases frame <;> cases eq
  case unwind frame _ _ => cases frame <;> cases eq
  all_goals cases eq

theorem Step.handle_raise_iff {raised caught : Name} {recovery : Expr Name}
    {s : Store} {target : Config Name} :
    Step ⟨.handle (.raise raised) caught recovery, s⟩ target ↔
      (raised = caught ∧ target = ⟨recovery, s⟩) ∨
      (raised ≠ caught ∧ target = ⟨.raise raised, s⟩) := by
  constructor
  · intro step
    generalize eq : (⟨.handle (.raise raised) caught recovery, s⟩ : Config Name) = before at step
    cases step
    case frame frame _ _ _ _ _ => cases frame <;> cases eq
    case unwind frame _ _ => cases frame <;> cases eq
    case handleStep inner => cases eq; exact (raise_terminal _ _ _ inner).elim
    case handleValue value => cases eq; cases value
    case catchRaise => cases eq; exact Or.inl ⟨rfl, rfl⟩
    case miss different => cases eq; exact Or.inr ⟨different, rfl⟩
    all_goals cases eq
  · rintro (⟨rfl, rfl⟩ | ⟨different, rfl⟩)
    · exact .catchRaise
    · exact .miss different

/-- Both handling a matching tag and forwarding a different tag preserve
the result type assigned to the protected computation. -/
theorem Step.handle_raise_typed {raised caught : Name} {recovery : Expr Name}
    {Θ : LocTypes} {Γ : List Ty} {T : Ty} {s : Store} {target : Config Name}
    (typed : HasType Θ Γ (.handle (.raise raised) caught recovery) T)
    (step : Step ⟨.handle (.raise raised) caught recovery, s⟩ target) :
    HasType Θ Γ target.expr T := by
  cases typed with
  | handle _ recoveryTyped =>
    rcases handle_raise_iff.mp step with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact recoveryTyped
    · exact .raise raised

theorem Steps.handle {body body' recovery : Expr Name} {name : Name} {s t : Store}
    (path : Steps ⟨body, s⟩ ⟨body', t⟩) :
    Steps ⟨.handle body name recovery, s⟩ ⟨.handle body' name recovery, t⟩ := by
  let wrap : Config Name → Config Name := fun c => ⟨.handle c.expr name recovery, c.store⟩
  apply Relation.ReflTransGen.lift wrap ?_ _ _ path
  rintro ⟨_, _⟩ ⟨_, _⟩ step
  exact .handleStep step

end Silmaril.Courses.Cambridge.L3.Exercises.Exceptions
