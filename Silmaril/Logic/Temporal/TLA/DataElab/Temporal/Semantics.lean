module

public import Silmaril.Logic.Temporal.TLA.DataElab.Defs
public import Silmaril.Logic.Temporal.TLA.Defs

/-! Denotations for the nonquantified temporal fragment of named data expressions. -/

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

/-- A scalar or tuple of state expressions used only for observation equality. -/
abbrev Observation (signature : ExternalSignature) := List (CheckedExpr signature)

noncomputable def Observation.eval (observation : Observation signature)
    (I : Interpretation V signature) (ρ : RigidEnv V) : StateExpr (State V) (List V) :=
  fun s => observation.map fun e => e.eval I.data I.booleans I.external ⟨ρ, s⟩

/-- Values of predicates in state and step positions. Source atoms use the
existing data interpretation, and action operators reify propositions. -/
inductive Predicate (signature : ExternalSignature) where
  | data (expression : CheckedExpr signature)
  | neg (p : Predicate signature)
  | binary (op : Logic) (p q : Predicate signature)
  | junction (kind : Surface.Junction) (items : List (Predicate signature))
  | unchanged (obs : Observation signature)
  | bracket (kind : Surface.ActionBracket) (p : Predicate signature) (obs : Observation signature)
  | enabled (p : Predicate signature)

open Classical in
mutual

noncomputable def Predicate.eval (I : Interpretation V signature) (ρ : RigidEnv V)
    (p : Predicate signature) (s t : State V) : V :=
  let B := I.booleans
  match p with
  | .data e => e.term.eval I.data B I.external ⟨ρ, s⟩ (fun _ => I.data.enum []) t
  | .neg p =>
    let value := p.eval I ρ s t
    if B.IsBoolean value then B.ofProp (¬B.holds value) else B.invalid .negation [value]
  | .binary op p q => op.eval B (p.eval I ρ s t) (q.eval I ρ s t)
  | .junction kind items =>
    let values := Predicate.evalList I ρ items s t
    let (absorbing, identity) := match kind with
      | .conjunction => (B.falseValue, B.trueValue)
      | .disjunction => (B.trueValue, B.falseValue)
    if absorbing ∈ values then absorbing
    else if ∀ value ∈ values, B.IsBoolean value then identity
    else B.invalid (.junction kind) values
  | .unchanged obs => B.ofProp (Action.unchanged (obs.eval I ρ) s t)
  | .bracket kind p obs =>
    let A : Action (State V) := fun source target => B.holds (p.eval I ρ source target)
    let f := obs.eval I ρ
    B.ofProp (match kind with
      | .square => A.bracket f s t
      | .angle => A.angle f s t)
  | .enabled p => B.ofProp (Action.enabled (fun source target => B.holds (p.eval I ρ source target)) s)
termination_by structural p

noncomputable def Predicate.evalList (I : Interpretation V signature) (ρ : RigidEnv V)
    (items : List (Predicate signature)) (s t : State V) : List V :=
  match items with
  | [] => []
  | p :: rest => p.eval I ρ s t :: Predicate.evalList I ρ rest s t
termination_by structural items

end

noncomputable def Predicate.toAction (p : Predicate signature) (I : Interpretation V signature)
    (ρ : RigidEnv V) : Action (State V) :=
  fun s t => I.booleans.holds (p.eval I ρ s t)

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

noncomputable def Form.toFormula (form : Form signature) (I : Interpretation V signature)
    (ρ : RigidEnv V) : Formula (State V) :=
  match form with
  | .state p => .state (p.toStatePred I ρ)
  | .neg p => .neg (p.toFormula I ρ)
  | .binary op p q => Form.binaryFormula op (p.toFormula I ρ) (q.toFormula I ρ)
  | .junction kind items => Form.junctionFormula kind items I ρ
  | .always p => .always (p.toFormula I ρ)
  | .eventually p => (p.toFormula I ρ).eventually
  | .leadsTo p q => (p.toFormula I ρ).leadsTo (q.toFormula I ρ)
  | .alwaysBracket p obs => .alwaysBracket (p.toAction I ρ) (obs.eval I ρ)
  | .eventuallyAngle p obs => .eventuallyAngle (p.toAction I ρ) (obs.eval I ρ)
  | .fairness .weak p obs => .weakFair (p.toAction I ρ) (obs.eval I ρ)
  | .fairness .strong p obs => .strongFair (p.toAction I ρ) (obs.eval I ρ)
termination_by structural form

noncomputable def Form.junctionFormula (kind : Surface.Junction) (items : List (Form signature))
    (I : Interpretation V signature) (ρ : RigidEnv V) : Formula (State V) :=
  match items with
  | [] => .state fun _ => match kind with | .conjunction => True | .disjunction => False
  | p :: rest =>
    let op := match kind with | .conjunction => Logic.and | .disjunction => .or
    Form.binaryFormula op (p.toFormula I ρ) (Form.junctionFormula kind rest I ρ)
termination_by structural items

end

end
end Silmaril.Logic.Temporal.TLA.DataElab.Temporal
