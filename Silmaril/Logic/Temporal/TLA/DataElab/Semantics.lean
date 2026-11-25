module

public import Silmaril.Logic.Temporal.TLA.Data.Defs
public import Silmaril.Logic.Temporal.TLA.Resolution.Defs

/-! The expanded data expressions and their mathematical interpretation. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab

@[expose] public section

open Resolution

universe u

/-- The admitted external declaration identities and their expression arities. -/
abbrev ExternalSignature := BindingId → Option Nat

/-- An interpretation of an external declaration with a caller-stated contract. -/
structure Primitive (V : Type u) (arity : Nat) where
  apply : List V → V
  spec : List V → V → Prop
  sound : ∀ args, args.length = arity → spec args (apply args)

abbrev ExternalInterpretation (V : Type u) (signature : ExternalSignature) :=
  (id : BindingId) → (arity : Nat) → signature id = some arity → Primitive V arity

inductive Logic where
  | and | or | implies | equiv
  deriving DecidableEq, Repr

inductive BooleanContext where
  | negation
  | binary (op : Logic)
  | junction (kind : Surface.Junction)
  | conditional
  deriving Repr

/-- Boolean values and the caller's policies for non-Boolean inputs. Binder
predicates use `holds`. Logical operators and IF use `invalid` when
the Boolean inputs do not determine the result. -/
structure Booleans (V : Type u) where
  trueValue : V
  falseValue : V
  holds : V → Prop
  holds_true : holds trueValue
  not_holds_false : ¬ holds falseValue
  invalid : BooleanContext → List V → V

namespace Booleans

variable {V : Type u}

open Classical in
noncomputable def ofProp (B : Booleans V) (p : Prop) : V :=
  if p then B.trueValue else B.falseValue

@[simp] theorem ofProp_true (B : Booleans V) : B.ofProp True = B.trueValue := ite_eq_left trivial

@[simp] theorem ofProp_false (B : Booleans V) : B.ofProp False = B.falseValue := ite_eq_right not_false

def IsBoolean (B : Booleans V) (value : V) : Prop :=
  value = B.trueValue ∨ value = B.falseValue

theorem holds_ofProp (B : Booleans V) (p : Prop) : B.holds (B.ofProp p) ↔ p := by
  classical
  by_cases p <;> simp_all [ofProp, B.holds_true, B.not_holds_false]

end Booleans

/-- Rigid constants use the same assignment at every state. The flexible
assignment supplies one state's values for variable declarations. -/
structure Valuation (V : Type u) where
  rigid : BindingId → V
  flexible : BindingId → V

/-- Expanded data syntax. A witness slot is fresh at each binder expansion.
The external node carries the admitted declaration identity and actual arity. -/
inductive Term (signature : ExternalSignature) where
  | rigid (id : BindingId)
  | flexible (id : BindingId)
  | witness (slot : Nat)
  | boolean (value : Bool)
  | booleanSet
  | eq (negated : Bool) (left right : Term signature)
  | mem (negated : Bool) (element set : Term signature)
  | not (arg : Term signature)
  | logic (op : Logic) (left right : Term signature)
  | junction (kind : Surface.Junction) (args : List (Term signature))
  | ite (condition yes no : Term signature)
  | enum (items : List (Term signature))
  | filter (slot : Nat) (bound body : Term signature)
  | image (slot : Nat) (bound body : Term signature)
  | quant (kind : Surface.Quantifier) (slot : Nat) (bound : Option (Term signature))
      (body : Term signature)
  | choose (slot : Nat) (bound : Option (Term signature)) (body : Term signature)
  | external (id : BindingId) (arity : Nat) (admitted : signature id = some arity)
      (args : List (Term signature))
  deriving Repr

variable {V : Type u} {signature : ExternalSignature}

mutual

/-- Check the expanded witness scopes and external argument counts. -/
def Term.isWellFormed (term : Term signature) (scope : List Nat) : Bool :=
  match term with
  | .rigid _ | .flexible _ | .boolean _ | .booleanSet => true
  | .witness slot => scope.contains slot
  | .eq _ l r | .mem _ l r | .logic _ l r => l.isWellFormed scope && r.isWellFormed scope
  | .not arg => arg.isWellFormed scope
  | .ite c y n => c.isWellFormed scope && y.isWellFormed scope && n.isWellFormed scope
  | .junction _ args | .enum args => argsWellFormed args scope
  | .filter slot bound body | .image slot bound body =>
    !scope.contains slot && bound.isWellFormed scope && body.isWellFormed (slot :: scope)
  | .quant _ slot bound body | .choose slot bound body =>
    let domainOk := match bound with
      | none => true
      | some domain => domain.isWellFormed scope
    !scope.contains slot && domainOk && body.isWellFormed (slot :: scope)
  | .external _ arity _ args => args.length == arity && argsWellFormed args scope
termination_by structural term

def Term.argsWellFormed (args : List (Term signature)) (scope : List Nat) : Bool :=
  match args with
  | [] => true
  | arg :: rest => arg.isWellFormed scope && argsWellFormed rest scope
termination_by structural args

end

def Logic.holds (op : Logic) (p q : Prop) : Prop :=
  match op with
  | .and => p ∧ q
  | .or => p ∨ q
  | .implies => p → q
  | .equiv => p ↔ q

open Classical in
/-- Boolean operands and absorbing values determine the usual result.
The interpretation supplies the value in the other cases. -/
noncomputable def Logic.eval (op : Logic) (B : Booleans V) (left right : V) : V :=
  let general :=
    if B.IsBoolean left ∧ B.IsBoolean right then B.ofProp (op.holds (B.holds left) (B.holds right))
    else B.invalid (.binary op) [left, right]
  match op with
  | .and => if left = B.falseValue ∨ right = B.falseValue then B.falseValue else general
  | .or => if left = B.trueValue ∨ right = B.trueValue then B.trueValue else general
  | .implies => if left = B.falseValue ∨ right = B.trueValue then B.trueValue else general
  | .equiv => general

/-- Assign a value to a witness slot while evaluating its scope. -/
def withWitness (witnesses : Nat → V) (slot : Nat) (value : V) : Nat → V :=
  fun i => if i = slot then value else witnesses i

open Classical

mutual

noncomputable def Term.eval (M : Data.Model V) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V)
    (term : Term signature) (witnesses : Nat → V) : V :=
  let truth := fun negated (p : Prop) => B.ofProp (if negated then ¬p else p)
  match term with
  | .rigid id => valuation.rigid id
  | .flexible id => valuation.flexible id
  | .witness slot => witnesses slot
  | .boolean value => if value then B.trueValue else B.falseValue
  | .booleanSet => M.enum [B.trueValue, B.falseValue]
  | .eq negated left right =>
    let l := eval M B external valuation left witnesses
    let r := eval M B external valuation right witnesses
    truth negated (l = r)
  | .mem negated element set =>
    truth negated (M.mem (eval M B external valuation element witnesses)
      (eval M B external valuation set witnesses))
  | .not arg =>
    let value := eval M B external valuation arg witnesses
    if B.IsBoolean value then B.ofProp (¬B.holds value) else B.invalid .negation [value]
  | .logic op left right =>
    let l := eval M B external valuation left witnesses
    let r := eval M B external valuation right witnesses
    op.eval B l r
  | .junction kind args =>
    let values := evalList M B external valuation args witnesses
    let (absorbing, identity) := match kind with
      | .conjunction => (B.falseValue, B.trueValue)
      | .disjunction => (B.trueValue, B.falseValue)
    if absorbing ∈ values then absorbing
    else if ∀ value ∈ values, B.IsBoolean value then identity
    else B.invalid (.junction kind) values
  | .ite condition yes no =>
    let value := eval M B external valuation condition witnesses
    let consequent := eval M B external valuation yes witnesses
    let alternative := eval M B external valuation no witnesses
    if B.IsBoolean value then
      if B.holds value then consequent else alternative
    else B.invalid .conditional [value, consequent, alternative]
  | .enum items => M.enum (evalList M B external valuation items witnesses)
  | .filter slot bound body =>
    M.sep (eval M B external valuation bound witnesses)
      (fun x => B.holds (eval M B external valuation body (withWitness witnesses slot x)))
  | .image slot bound body =>
    M.image (eval M B external valuation bound witnesses)
      (fun x => eval M B external valuation body (withWitness witnesses slot x))
  | .quant kind slot bound body =>
    let predicate := fun x => B.holds (eval M B external valuation body (withWitness witnesses slot x))
    B.ofProp (match kind, bound with
      | .exists, none => M.existsValue predicate
      | .forall, none => M.forallValue predicate
      | .exists, some domain => M.existsIn (eval M B external valuation domain witnesses) predicate
      | .forall, some domain => M.forallIn (eval M B external valuation domain witnesses) predicate)
  | .choose slot bound body =>
    let predicate := fun x => B.holds (eval M B external valuation body (withWitness witnesses slot x))
    match bound with
    | none => M.choose predicate
    | some domain => M.chooseIn (eval M B external valuation domain witnesses) predicate
  | .external id arity admitted args =>
    (external id arity admitted).apply (evalList M B external valuation args witnesses)
termination_by structural term

noncomputable def Term.evalList (M : Data.Model V) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V)
    (terms : List (Term signature)) (witnesses : Nat → V) : List V :=
  match terms with
  | [] => []
  | item :: rest =>
    eval M B external valuation item witnesses :: evalList M B external valuation rest witnesses
termination_by structural terms

end

end
end Silmaril.Logic.Temporal.TLA.DataElab
