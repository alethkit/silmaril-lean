module

public import Silmaril.SSA.Peggy.EPEG.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Sound

public section

namespace Silmaril.SSA.Peggy.EPEG

open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : PEG.InstructionSet.{u,v} Data}
variable {params results : List (PEG.Ty Data)} {n n' l : Nat}
variable {g : PEG.Graph P params results n l} {m : PEG.Interpretation.{u,v,x} P}
variable {values : g.Valuation m} {env : Tuple m.Value params}

theorem Classes.discrete_valid : (Classes.discrete (n := n)).Valid values := by
  intro a b h
  cases (show a = b from h)
  exact ⟨rfl, fun _ => HEq.rfl⟩

theorem Classes.merge_equates (classes : Classes n) (a b : Fin n) :
    classes.merge a b a = classes.merge a b b := by
  simp [Classes.merge]

theorem Classes.merge_preserves (classes : Classes n) (a b : Fin n) {p q : Fin n}
    (same : classes p = classes q) : classes.merge a b p = classes.merge a b q := by
  by_cases h : classes q = classes b <;> simp [Classes.merge, same, h]

/-- Merge using independently justified, same-sort equality at every index. -/
theorem Classes.merge_sound {classes : Classes n} {a b : Fin n}
    (valid : classes.Valid values) (evidence : StreamEq values a b) :
    (classes.merge a b).Valid values :=
  Silmaril.Proofs.SSA.Peggy.EPEG.merge_sound valid evidence

/-- Replay checks class membership for the guards. The supplied law must
establish the conclusion on the valuation whenever those guards hold. -/
theorem GuardedEquation.merge_sound {classes : Classes n} (rule : GuardedEquation g)
    (valid : classes.Valid values) (law : rule.Holds values) (check : rule.check classes = true) :
    (classes.merge rule.conclusion.lhs rule.conclusion.rhs).Valid values :=
  Silmaril.Proofs.SSA.Peggy.EPEG.merge_guarded_sound rule valid law check

/-- Ordered operands agree at the indices used by the common label. A θ
uses its initial and feedback slots at their respective indices. Pass
uses every sample, and eval uses both the count at the original index
and the samples throughout its prefix and at the selected count. -/
theorem MatchingNodes.streamEq {a b : Fin n} (pair : MatchingNodes g a b)
    (solves : g.Solves m env values)
    (operands : ∀ k : Fin pair.inputs.length, StreamEq values
      (pair.lhsArgs.get (PEG.portAt pair.inputs k)).id
      (pair.rhsArgs.get (PEG.portAt pair.inputs k)).id) :
    StreamEq values a b :=
  Silmaril.Proofs.SSA.Peggy.EPEG.congruent_streams pair solves operands

theorem MatchingNodes.merge_sound {classes : Classes n} {a b : Fin n} (pair : MatchingNodes g a b)
    (solves : g.Solves m env values) (valid : classes.Valid values)
    (check : pair.checkOperands classes = true) : (classes.merge a b).Valid values :=
  Silmaril.Proofs.SSA.Peggy.EPEG.merge_congruent_sound pair solves valid check

variable {target : PEG.Graph P params results n' l}

theorem Selection.demandWellFounded {candidate : Selection g target} {classes : Classes n}
    (check : candidate.check classes = true) : WellFounded target.Demand :=
  Silmaril.Proofs.SSA.Peggy.EPEG.selection_demandWellFounded check

/-- The candidate has well-founded demands by its own check. Its equations
must hold on the selected source streams before uniqueness transfers
the source root observation to the candidate. -/
theorem Selection.observe_sound (candidate : Selection g target) {classes : Classes n}
    (sourceWF : WellFounded g.Demand) (valid : classes.Valid (g.denote m env sourceWF))
    (check : candidate.check classes = true)
    (solves : target.Solves m env (candidate.inherit (g.denote m env sourceWF))) (i : PEG.Index l) :
    g.observe m (g.denote m env sourceWF) i =
      target.observe m (target.denote m env (candidate.demandWellFounded check)) i :=
  Silmaril.Proofs.SSA.Peggy.EPEG.selection_sound candidate sourceWF
    (candidate.demandWellFounded check) valid check solves i

end Silmaril.SSA.Peggy.EPEG
