module

public import Silmaril.Logic.Temporal.TLA.Resolution.Names

/-! Compositional levels and call requirements for first-order TLA+ operators. -/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Resolution.Levels

inductive Level where
  | constant | state | action | temporal
  deriving DecidableEq, Repr

def Level.rank : Level → Nat
  | .constant => 0
  | .state => 1
  | .action => 2
  | .temporal => 3

def Level.atMost (level ceiling : Level) : Bool :=
  level.rank ≤ ceiling.rank

def Level.join (left right : Level) : Level :=
  if left.atMost right then right else left

def Level.meet (left right : Level) : Level :=
  if left.atMost right then left else right

/-- The maximum of a fixed floor and the levels of the indicated formals. -/
structure LevelTerm where
  floor : Level := .constant
  dependencies : List BindingId := []
  deriving DecidableEq, Repr

def LevelTerm.fixed (level : Level) : LevelTerm := ⟨level, []⟩

def LevelTerm.parameter (id : BindingId) : LevelTerm := ⟨.constant, [id]⟩

def LevelTerm.join (left right : LevelTerm) : LevelTerm :=
  ⟨left.floor.join right.floor,
    right.dependencies.foldl (fun deps id => if id ∈ deps then deps else deps ++ [id])
      left.dependencies⟩

def LevelTerm.eval (term : LevelTerm) (levels : BindingId → Level) : Level :=
  term.dependencies.foldl (fun level id => level.join (levels id)) term.floor

def LevelTerm.substitute (term : LevelTerm) (arguments : List (BindingId × LevelTerm)) :
    LevelTerm :=
  term.dependencies.foldl (fun result id =>
    result.join ((arguments.lookup id).getD (.parameter id))) (.fixed term.floor)

theorem LevelTerm.eval_fixed (level : Level) (levels : BindingId → Level) :
    (LevelTerm.fixed level).eval levels = level := rfl

inductive Condition where
  | atMost (term : LevelTerm) (ceiling : Level)
  | nonAction (term : LevelTerm)
  | noMixedActionTemporal (terms : List LevelTerm)
  | temporalQuantifierBound (body range : LevelTerm)
  deriving DecidableEq, Repr

def Condition.holds (condition : Condition) (levels : BindingId → Level) : Bool :=
  match condition with
  | .atMost term ceiling => (term.eval levels).atMost ceiling
  | .nonAction term => term.eval levels ≠ .action
  | .noMixedActionTemporal terms =>
    let actual := terms.map (·.eval levels)
    ¬ (.action ∈ actual ∧ .temporal ∈ actual)
  | .temporalQuantifierBound body range =>
    ¬ (body.eval levels = .temporal ∧ range.eval levels = .action)

def Condition.substitute (condition : Condition) (arguments : List (BindingId × LevelTerm)) :
    Condition :=
  match condition with
  | .atMost term ceiling => .atMost (term.substitute arguments) ceiling
  | .nonAction term => .nonAction (term.substitute arguments)
  | .noMixedActionTemporal terms => .noMixedActionTemporal (terms.map (·.substitute arguments))
  | .temporalQuantifierBound body range =>
    .temporalQuantifierBound (body.substitute arguments) (range.substitute arguments)

def Condition.dependsOnFormals : Condition → Bool
  | .atMost term ceiling => ceiling ≠ .temporal && !term.dependencies.isEmpty
  | .nonAction term => !term.dependencies.isEmpty
  | .noMixedActionTemporal terms => terms.any (! ·.dependencies.isEmpty)
  | .temporalQuantifierBound body range =>
    !body.dependencies.isEmpty || !range.dependencies.isEmpty

structure Requirement where
  /-- Site that introduced the requirement, including across imported calls. -/
  origin : Site
  condition : Condition
  deriving DecidableEq, Repr

def Requirement.substitute (requirement : Requirement)
    (arguments : List (BindingId × LevelTerm)) : Requirement :=
  { requirement with condition := requirement.condition.substitute arguments }

structure OperatorSummary where
  parameters : List BindingId
  result : LevelTerm
  requirements : List Requirement
  deriving DecidableEq, Repr

/-- Substitute positional actual levels. Captured formals remain symbolic, and
the caller must check the instantiated requirements. -/
def OperatorSummary.instantiate (summary : OperatorSummary) (arguments : List LevelTerm) :
    Option (LevelTerm × List Requirement) := do
  if arguments.length ≠ summary.parameters.length then none
  else
    let substitution := summary.parameters.zip arguments
    some (summary.result.substitute substitution, summary.requirements.map (·.substitute substitution))

/-- Independent upper bounds from cap requirements. Callers must also satisfy
the summary's relational and syntax requirements. -/
def OperatorSummary.maxArgumentLevels (summary : OperatorSummary) : List Level :=
  summary.parameters.map fun id =>
    summary.requirements.foldl (fun ceiling requirement =>
      match requirement.condition with
      | .atMost term bound => if id ∈ term.dependencies then ceiling.meet bound else ceiling
      | _ => ceiling) .temporal

/-- A positional signature for an operator with no source-level definition in
the registry. Each argument has a level ceiling and a result weight. -/
structure ArgumentLevel where
  maximum : Level
  contributes : Bool
  deriving DecidableEq, Repr

structure ExternalSignature where
  floor : Level
  arguments : List ArgumentLevel
  deriving DecidableEq, Repr

abbrev ExternalLevels := List (BindingId × ExternalSignature)

end Silmaril.Logic.Temporal.TLA.Resolution.Levels
