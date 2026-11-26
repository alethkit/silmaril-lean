module

public import Silmaril.SSA.PEG.Bridge.LambdaSSA.Defs
public import Silmaril.SSA.PEG.Simple.Thms
public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.LambdaSSA.Correctness

public section

namespace Silmaril.SSA.PEG.Bridge.LambdaSSA

open RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

universe u

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params results : List (Ty Data)} (g : ScopedDiamond P params results)

theorem ScopedDiamond.peg_wellFormed : g.toPEG.WellFormed :=
  (Source.build g).code.toGraph_wellFormed (Source.build g).refs

theorem ScopedDiamond.peg_wellFounded : WellFounded g.toPEG.Demand :=
  g.toPEG.demandWellFounded g.peg_wellFormed

/-- The generated region has one external exit carrying the ordered result type. -/
theorem ScopedDiamond.lower_hasType :
    g.lower.HasType (Diamond.LambdaSSA.initialContext (Target.sorts params))
      [Diamond.Arms.LambdaSSA.resultCode (Target.sorts results)] :=
  Diamond.Arms.LambdaSSA.lower_hasType (Target.graph g)

variable (m : TotalModel P) (input : Tuple m.toPEG.Value params)

/-- The chosen PEG root vector matches the ordered packet read from the
selected predecessor. Every slot is defined for a total primitive model. -/
theorem ScopedDiamond.observe_diamond (wf : WellFounded g.toPEG.Demand) (idx : Index 0) :
    g.toPEG.observe m.toPEG (g.toPEG.denote m.toPEG input wf) idx =
      (Target.unpack (F := Target.ValueAt m) results
        ((Target.graph g).denote (Target.model m) (Target.entry m input))).map (fun _ => some) :=
  Proofs.observe_lower m input g wf idx

/-- A finite λSSA evaluation exists exactly at exit zero with unchanged
ambient state and the typed packing of the defined Figure 11 root vector. -/
theorem ScopedDiamond.lower_eval_iff {σ : Type u} (wf : WellFounded g.toPEG.Demand)
    (idx : Index 0) (start finish : σ) (label : Nat)
    (payload : Value (Diamond.LambdaSSA.Atom (Target.model m))) :
    Semantics.Region.Eval (Diamond.LambdaSSA.instruction (Target.model m))
      (Diamond.LambdaSSA.inputEnv (Target.model m) (Target.entry m input)) g.lower
      start label payload finish ↔
      label = 0 ∧ finish = start ∧ ∃ result : Tuple m.toPEG.Value results,
        g.toPEG.observe m.toPEG (g.toPEG.denote m.toPEG input wf) idx = result.map (fun _ => some) ∧
        payload = Diamond.LambdaSSA.encodeTuple (Target.model m)
          (Target.pack (F := Target.ValueAt m) result) :=
  Proofs.lower_eval_iff m input g wf idx start finish label payload

end Silmaril.SSA.PEG.Bridge.LambdaSSA
