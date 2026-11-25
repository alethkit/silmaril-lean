module

public import Silmaril.Courses.Cambridge.L2.Reduction
public import Silmaril.Courses.Cambridge.OperationalInstitution.Basic

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.OperationalInstitution

open CategoryTheory Silmaril.Logic.Operational Silmaril.Semantics.Operational
open Silmaril.Courses.Cambridge.OperationalInstitution (ofLTS valueSemantics)

/-- The existing call-by-value L2 relation over its expressions and finite stores. -/
def system : TransitionSystem := ofLTS lts

theorem sat_iff (s t : Config) :
    (Signature.institution.obj system.shape).Sat (Discrete.mk system.model) (s, (), t) ↔
      Step s t :=
  Cambridge.OperationalInstitution.sat_iff lts s t ()

/-- Finite L2 returns retain the value expression, including lambdas, and final store. -/
def semantics : OpSem Config Config := valueSemantics lts (fun c => IsValue c.expr)

theorem terminalDiscipline : semantics.TerminalDiscipline :=
  fun ⟨_, _⟩ _ h => value_terminal h.1

theorem may_return_iff (s t : Config) :
    semantics.May s (.returned t) ↔ Steps s t ∧ IsValue t.expr :=
  Cambridge.OperationalInstitution.may_return_iff lts _ s t

end Silmaril.Courses.Cambridge.L2.OperationalInstitution
