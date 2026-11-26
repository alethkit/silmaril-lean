module

public import Silmaril.SSA.Peggy.Bridge.Figure11.Defs
public import Silmaril.SSA.Peggy.Bridge.Egg.Thms
import Silmaril.Proofs.SSA.Peggy.Bridge.Figure11.Correspondence

public section

namespace Silmaril.SSA.Peggy.Bridge.Figure11

open RVSDG (Tuple)
open Acyclic (Ranked)
open Silmaril.Logic.Egg

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params results : List (PEG.Ty Data)} {n n' : Nat}
variable {g : PEG.Graph P params results n 0} {g' : PEG.Graph P params results n' 0}

/-- A decreasing vertex rank also admits the graph to Figure 11's guarded denotation. -/
theorem demandWellFounded (r : Ranked g) : WellFounded g.Demand :=
  Silmaril.Proofs.SSA.Peggy.Bridge.Figure11.demandWellFounded r

/-- Exact nodewise agreement, with bottom retained by `liftPartial`. -/
theorem denote_eq_valuation (r : Ranked g) (m : PEG.Interpretation.{0,0,0} P)
    (env : Tuple m.Value params) (wf : WellFounded g.Demand) :
    g.denote m env wf = valuation r m env :=
  Silmaril.Proofs.SSA.Peggy.Bridge.Figure11.denote_eq_valuation m r env wf

theorem observe_get (r : Ranked g) (m : PEG.Interpretation.{0,0,0} P)
    (env : Tuple m.Value params) (wf : WellFounded g.Demand)
    (idx : PEG.Index 0) (i : Fin results.length) :
    (g.observe m (g.denote m env wf) idx).get (PEG.portAt results i) =
      liftPartial m (r.evalOutputs (toAcyclic m) (toInputs m env) i) :=
  Silmaril.Proofs.SSA.Peggy.Bridge.Figure11.observe_get m r env wf idx i

open Egg in
/-- Explained outputs have equal native observations, including certificates
composed from several replayed steps. -/
theorem outputs_figure11_sound
    {rs : List (Core.Rule (signature P))} {r : Ranked g} {r' : Ranked g'}
    (certificate : OutputsExplained rs r r')
    (m : PEG.Interpretation.{0,0,0} P) (hrules : ∀ rule ∈ rs, rule.Holds (model (toAcyclic m)))
    (env : Tuple m.Value params) (wf : WellFounded g.Demand) (wf' : WellFounded g'.Demand)
    (idx : PEG.Index 0) :
    g.observe m (g.denote m env wf) idx = g'.observe m (g'.denote m env wf') idx :=
  Silmaril.Proofs.SSA.Peggy.Bridge.Figure11.outputs_figure11_sound m certificate hrules env wf wf' idx

open Egg in
/-- Accepted Egg receipts give equality of the actual Figure 11 root tuples.
Rules retain their existing partial-carrier satisfaction hypotheses. -/
theorem checkOutputs_figure11_sound [DecidableEq Data] (eqPrim : PrimitiveEq P)
    {rs : List (Core.Rule (signature P))} {r : Ranked g} {r' : Ranked g'}
    {receipts : ∀ i : Fin results.length, Core.Replay.Receipt rs (context params) results[i]}
    (accepted : (checkOutputs eqPrim r r' receipts).isSome)
    (m : PEG.Interpretation.{0,0,0} P) (hrules : ∀ rule ∈ rs, rule.Holds (model (toAcyclic m)))
    (env : Tuple m.Value params) (wf : WellFounded g.Demand) (wf' : WellFounded g'.Demand)
    (idx : PEG.Index 0) :
    g.observe m (g.denote m env wf) idx = g'.observe m (g'.denote m env wf') idx :=
  outputs_figure11_sound ((checkOutputs eqPrim r r' receipts).get accepted).down
    m hrules env wf wf' idx

end Silmaril.SSA.Peggy.Bridge.Figure11
