module

public import Silmaril.SSA.Peggy.Optimizer.Defs
public import Silmaril.SSA.Peggy.Optimizer.Extension.Thms
import Silmaril.Proofs.SSA.Peggy.Optimizer.Sound

public section

namespace Silmaril.SSA.Peggy.Optimizer

open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egg
open Bridge.Egg Bridge.Figure11
open RVSDG (Tuple)

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params results : List (PEG.Ty Data)} {out : PEG.Ty Data}
variable {p : Program P params out} {r : Rule P out} {rs : List (Rule P out)}

/-- A discovered binding instantiates the supplied law at the exact
matched term when the instantiated guard equalities hold. -/
theorem TermMatch.sound {source : RankedProgram P params results} {target : Term P params out}
    (found : TermMatch source r target) (M : Core.Model (signature P))
    (env : ∀ i, M.carrier (context params i)) (law : r.core.Holds M)
    (guards : ∀ e ∈ r.guards,
      (Core.Pattern.instantiate (termSub found.binding) e.lhs).eval M env =
        (Core.Pattern.instantiate (termSub found.binding) e.rhs).eval M env) :
    target.eval M env =
      (Core.Pattern.instantiate (termSub found.binding) r.rhs.term).eval M env :=
  Silmaril.Proofs.SSA.Peggy.Optimizer.match_sound found M env law guards

/-- A discovered binding makes the rule's instantiated left side exactly the
current root. Applying its law still needs the instantiated guard equalities. -/
theorem RootMatch.sound (found : RootMatch p r) (M : Core.Model (signature P))
    (env : ∀ i, M.carrier (context params i)) (law : r.core.Holds M)
    (guards : ∀ e ∈ r.guards,
      (Core.Pattern.instantiate (termSub found.binding) e.lhs).eval M env =
        (Core.Pattern.instantiate (termSub found.binding) e.rhs).eval M env) :
    (encodeOutputs p.ranked 0).eval M env =
      (Core.Pattern.instantiate (termSub found.binding) r.rhs.term).eval M env :=
  TermMatch.sound found M env law guards

/-- A verified or composed explanation preserves the native ordered
Figure 11 observations for every interpretation satisfying its table. -/
theorem CheckedProgram.sound {rules : List (Core.Rule (signature P))}
    {source : RankedProgram P params results} (candidate : CheckedProgram rules source)
    (m : PEG.Interpretation.{0,0,0} P) (laws : ∀ rule ∈ rules, rule.Holds (model (toAcyclic m)))
    (env : Tuple m.Value params) (idx : PEG.Index 0) :
    source.graph.observe m (source.graph.denote m env (demandWellFounded source.ranked)) idx =
      candidate.program.graph.observe m (candidate.program.graph.denote m env
        (demandWellFounded candidate.program.ranked)) idx :=
  outputs_figure11_sound candidate.explained m laws env
    (demandWellFounded source.ranked) (demandWellFounded candidate.program.ranked) idx

/-- Candidates reached by replay and its transitive composition preserve the
actual Figure 11 observation for every interpretation satisfying the table. -/
theorem Candidate.sound (candidate : Candidate rs p) (m : PEG.Interpretation.{0,0,0} P)
    (laws : ∀ rule ∈ coreRules rs, rule.Holds (model (toAcyclic m)))
    (env : Tuple m.Value params) (idx : PEG.Index 0) :
    p.graph.observe m (p.graph.denote m env (demandWellFounded p.ranked)) idx =
      candidate.program.graph.observe m (candidate.program.graph.denote m env
        (demandWellFounded candidate.program.ranked)) idx :=
  CheckedProgram.sound candidate m laws env idx

theorem optimize_mem [DecidableEq Data] (eqPrim : PrimitiveEq P) (rs : List (Rule P out))
    (fuel : Nat) (p : Program P params out) :
    optimize eqPrim rs fuel p ∈ explore eqPrim rs fuel p :=
  Silmaril.Proofs.SSA.Peggy.Optimizer.optimize_mem eqPrim rs fuel p

/-- Optimality is relative to the candidates in the bounded, replay-checked
search and the stated unfolded application count. -/
theorem optimize_min [DecidableEq Data] (eqPrim : PrimitiveEq P) (rs : List (Rule P out))
    (fuel : Nat) (p : Program P params out) {candidate : Candidate rs p}
    (mem : candidate ∈ explore eqPrim rs fuel p) :
    (optimize eqPrim rs fuel p).program.cost ≤ candidate.program.cost :=
  Silmaril.Proofs.SSA.Peggy.Optimizer.fold_le_member Program.cost _ _ mem

end Silmaril.SSA.Peggy.Optimizer
