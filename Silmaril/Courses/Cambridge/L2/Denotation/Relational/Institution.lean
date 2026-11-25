module

public import Silmaril.Courses.Cambridge.L2.Denotation.Relational.Adequacy
public import Silmaril.Courses.Cambridge.L2.Denotation.EffectfulAdequacy
public import Silmaril.Courses.Cambridge.L2.OperationalInstitution
public import Silmaril.Logic.Fragments.Institution.Thms

/-! # Finite return observations and agreement on the earlier fragment -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.RelationalDenotation

open CategoryTheory Silmaril.Logic.Fragments Silmaril.Semantics.Operational

def signature : AtomicSignature := ⟨Config × Config⟩

def model : AtomicModel signature :=
  fun (source, target) => Observes [] source.expr source.store target

theorem sat_iff (source target : Config) :
    (atomicInstitution.obj signature).Sat (Discrete.mk model) (source, target) ↔
      OperationalInstitution.semantics.May source (.returned target) := by
  cases source with
  | mk e s => exact (adequate e s target).trans (OperationalInstitution.may_return_iff _ _).symm

/-- The two denotations agree on ground returns of the typed loop-free,
nonrecursive fragment from covering stores. -/
theorem agrees_effectful {locations : L1.TypeEnv} {e : Expr} {T : Ty} {s : Store}
    (term : EffectfulDenotation.Term locations [] e T)
    (ground : PureDenotation.Ground T) (covers : EffectfulDenotation.Covers locations s)
    (target : Config) :
    Observes [] e s target ↔ target ∈ term.observe ground s :=
  (adequate e s target).trans (term.adequate ground covers target).symm

end Silmaril.Courses.Cambridge.L2.RelationalDenotation
