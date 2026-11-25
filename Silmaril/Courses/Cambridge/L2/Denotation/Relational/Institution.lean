module

public import Silmaril.Courses.Cambridge.L2.Denotation.Relational.Adequacy
public import Silmaril.Courses.Cambridge.L2.Denotation.EffectfulAdequacy
public import Silmaril.Courses.Cambridge.L2.OperationalInstitution
public import Silmaril.Logic.Fragments.Institution.Thms
import Silmaril.Courses.Cambridge.L2.Denotation.Operational
import Silmaril.Courses.Cambridge.L2.Metatheory.Progress

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

/-- Progress and preservation identify absence of a finite return with an
infinite trace on closed, well-typed inputs with a covering store. -/
theorem no_observation_iff_infinite {Γ : TypeEnv} {e : Expr} {T : Ty} {s : Store}
    (typed : HasType Γ e T) (closed : e.Closed) (covers : StoreCovers Γ s) :
    (∀ target, ¬ Observes [] e s target) ↔ InfiniteTrace Step ⟨e, s⟩ := by
  constructor
  · intro absent
    apply InfiniteTrace.coinduct (Steps ⟨e, s⟩) ?_ .refl
    intro current path
    have safe : HasType Γ current.expr T ∧ current.expr.Closed ∧ StoreCovers Γ current.store := by
      induction path with
      | refl => exact ⟨typed, closed, covers⟩
      | tail _ next ih =>
        exact ⟨next.preserves_type ih.1, next.preserves_closed ih.2.1, next.preserves_coverage ih.2.2⟩
    rcases progress safe.1 safe.2.1 safe.2.2 with ready | ⟨next, step⟩
    · exact (absent current ((adequate e s current).mpr ⟨path, ready⟩)).elim
    · exact ⟨next, step, path.tail step⟩
  · intro infinite target observed
    obtain ⟨path, ready⟩ := (adequate e s target).mp observed
    cases target
    exact (RightUnique.not_infinite_of_final Denotation.stepRightUnique path
      (value_terminal ready)) infinite

end Silmaril.Courses.Cambridge.L2.RelationalDenotation
