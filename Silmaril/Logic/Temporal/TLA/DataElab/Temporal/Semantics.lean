module

public import Silmaril.Logic.Temporal.TLA.DataElab.Defs
public import Silmaril.Logic.Temporal.TLA.Defs

/-! Denotations for the temporal fragment of named data expressions. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Temporal

open Resolution

@[expose] public section

universe u

/-- Every flexible declaration can take any value in the interpretation. -/
abbrev State (V : Type u) := BindingId → V
abbrev RigidEnv (V : Type u) := BindingId → V

/-- Fix these operations and primitive interpretations throughout a behavior. -/
structure Interpretation (V : Type u) (signature : ExternalSignature) where
  data : DataOperations V
  booleans : Booleans V
  external : ExternalInterpretation V signature

variable {V : Type u} {signature : ExternalSignature}

abbrev Witnesses (V : Type u) := Nat → V

/-- A data leaf checked against the enclosing temporal witness slots. -/
structure ScopedExpr (signature : ExternalSignature) where
  term : Term signature
  slots : List Nat
  wellFormed : term.isWellFormed slots = true

noncomputable def ScopedExpr.eval (e : ScopedExpr signature) (I : Interpretation V signature)
    (ρ : RigidEnv V) (witnesses : Witnesses V) (s t : State V) : V :=
  e.term.eval I.data I.booleans I.external ⟨ρ, s⟩ witnesses t

/-- A scalar or tuple of state expressions used only for observation equality. -/
abbrev Observation (signature : ExternalSignature) := List (ScopedExpr signature)

noncomputable def Observation.evalWith (observation : Observation signature)
    (I : Interpretation V signature) (ρ : RigidEnv V) (witnesses : Witnesses V) :
    StateExpr (State V) (List V) :=
  fun s => observation.map fun e => e.eval I ρ witnesses s s

noncomputable def Observation.eval (observation : Observation signature)
    (I : Interpretation V signature) (ρ : RigidEnv V) : StateExpr (State V) (List V) :=
  observation.evalWith I ρ (fun _ => I.data.enum [])

/-- Values of predicates in state and step positions. Source atoms use the
existing data interpretation, and action operators reify propositions. -/
inductive Predicate (signature : ExternalSignature) where
  | data (expression : ScopedExpr signature)
  | neg (p : Predicate signature)
  | binary (op : Logic) (p q : Predicate signature)
  | junction (kind : Surface.Junction) (items : List (Predicate signature))
  | unchanged (obs : Observation signature)
  | bracket (kind : Surface.ActionBracket) (p : Predicate signature) (obs : Observation signature)
  | enabled (p : Predicate signature)

open Classical in
mutual

noncomputable def Predicate.evalWith (I : Interpretation V signature) (ρ : RigidEnv V)
    (witnesses : Witnesses V)
    (p : Predicate signature) (s t : State V) : V :=
  let B := I.booleans
  match p with
  | .data e => e.eval I ρ witnesses s t
  | .neg p =>
    let value := p.evalWith I ρ witnesses s t
    if B.IsBoolean value then B.ofProp (¬B.holds value) else B.invalid .negation [value]
  | .binary op p q => op.eval B (p.evalWith I ρ witnesses s t) (q.evalWith I ρ witnesses s t)
  | .junction kind items =>
    let values := Predicate.evalList I ρ witnesses items s t
    let (absorbing, identity) := match kind with
      | .conjunction => (B.falseValue, B.trueValue)
      | .disjunction => (B.trueValue, B.falseValue)
    if absorbing ∈ values then absorbing
    else if ∀ value ∈ values, B.IsBoolean value then identity
    else B.invalid (.junction kind) values
  | .unchanged obs => B.ofProp (Action.unchanged (obs.evalWith I ρ witnesses) s t)
  | .bracket kind p obs =>
    let A : Action (State V) := fun source target => B.holds (p.evalWith I ρ witnesses source target)
    let f := obs.evalWith I ρ witnesses
    B.ofProp (match kind with
      | .square => A.bracket f s t
      | .angle => A.angle f s t)
  | .enabled p => B.ofProp (Action.enabled (fun source target => B.holds (p.evalWith I ρ witnesses source target)) s)
termination_by structural p

noncomputable def Predicate.evalList (I : Interpretation V signature) (ρ : RigidEnv V)
    (witnesses : Witnesses V)
    (items : List (Predicate signature)) (s t : State V) : List V :=
  match items with
  | [] => []
  | p :: rest => p.evalWith I ρ witnesses s t :: Predicate.evalList I ρ witnesses rest s t
termination_by structural items

end

noncomputable def Predicate.eval (I : Interpretation V signature) (ρ : RigidEnv V)
    (p : Predicate signature) (s t : State V) : V :=
  p.evalWith I ρ (fun _ => I.data.enum []) s t

noncomputable def Predicate.actionWith (p : Predicate signature) (I : Interpretation V signature)
    (ρ : RigidEnv V) (witnesses : Witnesses V) : Action (State V) :=
  fun s t => I.booleans.holds (p.evalWith I ρ witnesses s t)

noncomputable def Predicate.toAction (p : Predicate signature) (I : Interpretation V signature)
    (ρ : RigidEnv V) : Action (State V) :=
  p.actionWith I ρ (fun _ => I.data.enum [])

noncomputable def Predicate.toStatePred (p : Predicate signature) (I : Interpretation V signature)
    (ρ : RigidEnv V) : StatePred (State V) :=
  fun s => p.toAction I ρ s s

/-- Only a square or angle modality can turn a step predicate into a formula.
Fairness applies to the changing steps of the given action and observation. -/
inductive Form (signature : ExternalSignature) where
  | state (p : Predicate signature)
  | neg (p : Form signature)
  | binary (op : Logic) (p q : Form signature)
  | junction (kind : Surface.Junction) (items : List (Form signature))
  | rigidQuant (kind : Surface.Quantifier) (slot : Nat) (bound : Option (ScopedExpr signature))
      (body : Form signature)
  | always (p : Form signature)
  | eventually (p : Form signature)
  | leadsTo (p q : Form signature)
  | alwaysBracket (p : Predicate signature) (obs : Observation signature)
  | eventuallyAngle (p : Predicate signature) (obs : Observation signature)
  | fairness (kind : Surface.Fairness) (p : Predicate signature) (obs : Observation signature)

def Form.binaryFormula {S : Type u} (op : Logic) (p q : Formula S) : Formula S :=
  match op with
  | .and => .conj p q
  | .or => p.disj q
  | .implies => p.imp q
  | .equiv => .conj (p.imp q) (q.imp p)

mutual

noncomputable def Form.toFormulaWith (form : Form signature) (I : Interpretation V signature)
    (ρ : RigidEnv V) (witnesses : Witnesses V) : Formula (State V) :=
  match form with
  | .state p => .state (fun s => p.actionWith I ρ witnesses s s)
  | .neg p => .neg (p.toFormulaWith I ρ witnesses)
  | .binary op p q => Form.binaryFormula op (p.toFormulaWith I ρ witnesses) (q.toFormulaWith I ρ witnesses)
  | .junction kind items => Form.junctionFormula kind items I ρ witnesses
  | .rigidQuant kind slot bound body =>
    let instantiate := fun value => body.toFormulaWith I ρ (withWitness witnesses slot value)
    let guard := fun (e : ScopedExpr signature) value =>
      Formula.state fun s => I.data.mem value (e.eval I ρ witnesses s s)
    match kind, bound with
    | .exists, none => .existsRigid instantiate
    | .forall, none => .forallRigid instantiate
    | .exists, some e => .existsRigid fun value => .conj (guard e value) (instantiate value)
    | .forall, some e => .forallRigid fun value => (guard e value).imp (instantiate value)
  | .always p => .always (p.toFormulaWith I ρ witnesses)
  | .eventually p => (p.toFormulaWith I ρ witnesses).eventually
  | .leadsTo p q => (p.toFormulaWith I ρ witnesses).leadsTo (q.toFormulaWith I ρ witnesses)
  | .alwaysBracket p obs => .alwaysBracket (p.actionWith I ρ witnesses) (obs.evalWith I ρ witnesses)
  | .eventuallyAngle p obs => .eventuallyAngle (p.actionWith I ρ witnesses) (obs.evalWith I ρ witnesses)
  | .fairness .weak p obs => .weakFair (p.actionWith I ρ witnesses) (obs.evalWith I ρ witnesses)
  | .fairness .strong p obs => .strongFair (p.actionWith I ρ witnesses) (obs.evalWith I ρ witnesses)
termination_by structural form

noncomputable def Form.junctionFormula (kind : Surface.Junction) (items : List (Form signature))
    (I : Interpretation V signature) (ρ : RigidEnv V) (witnesses : Witnesses V) : Formula (State V) :=
  match items with
  | [] => .state fun _ => match kind with | .conjunction => True | .disjunction => False
  | p :: rest =>
    let op := match kind with | .conjunction => Logic.and | .disjunction => .or
    Form.binaryFormula op (p.toFormulaWith I ρ witnesses) (Form.junctionFormula kind rest I ρ witnesses)
termination_by structural items

end

noncomputable def Form.toFormula (form : Form signature) (I : Interpretation V signature)
    (ρ : RigidEnv V) : Formula (State V) :=
  form.toFormulaWith I ρ (fun _ => I.data.enum [])

end
end Silmaril.Logic.Temporal.TLA.DataElab.Temporal
