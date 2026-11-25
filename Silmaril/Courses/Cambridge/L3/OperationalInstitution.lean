module

public import Silmaril.Courses.Cambridge.L3.Reduction
public import Silmaril.Courses.Cambridge.OperationalInstitution.Basic

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.OperationalInstitution

open CategoryTheory Silmaril.Logic.Operational Silmaril.Semantics.Operational
open Silmaril.Courses.Cambridge.OperationalInstitution (ofLTS valueSemantics)

/-- The direct L3 rules over complete configurations, including every fresh allocation. -/
def lts : Cslib.LTS Config Unit := ⟨fun s _ t => Step s t⟩

def system : TransitionSystem := ofLTS lts

theorem sat_iff (s t : Config) :
    (Signature.institution.obj system.shape).Sat (Discrete.mk system.model) (s, (), t) ↔
      Step s t :=
  Cambridge.OperationalInstitution.sat_iff lts s t ()

theorem lts_unlabelled_iff (s t : Config) : lts.UnlabelledTr s t ↔ Step s t :=
  ⟨fun ⟨_, step⟩ => step, fun step => ⟨(), step⟩⟩

/-- Finite reachability in the institutional model agrees with closure of the direct rules. -/
theorem steps_iff_reachable (s t : Config) :
    Steps s t ↔ (Signature.toLTS system.model).CanReach s t := by
  change Steps s t ↔ lts.CanReach s t
  rw [← lts.reflTransGen_unlabelledTr_iff]
  exact ⟨Relation.ReflTransGen.mono (fun a b => (lts_unlabelled_iff a b).2) s t,
    Relation.ReflTransGen.mono (fun a b => (lts_unlabelled_iff a b).1) s t⟩

/-- Finite may returns report the complete value configuration with its concrete locations. -/
def semantics : OpSem Config Config := valueSemantics lts (fun c => IsValue c.expr)

private theorem value_no_step {e : Expr} (value : IsValue e) (s : Store) (t : Config) :
    ¬ Step ⟨e, s⟩ t := by
  induction value generalizing s t <;> intro step <;> cases step
  all_goals solve_by_elim

theorem terminalDiscipline : semantics.TerminalDiscipline :=
  fun ⟨_, s⟩ _ h t => value_no_step h.1 s t

theorem may_return_iff (s t : Config) :
    semantics.May s (.returned t) ↔ Steps s t ∧ IsValue t.expr :=
  Cambridge.OperationalInstitution.may_return_iff lts _ s t

end Silmaril.Courses.Cambridge.L3.OperationalInstitution
