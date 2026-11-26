module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Dataflow.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.Dataflow

/-! Monotonicity and concrete coverage of the shared abstract producer table. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP

open RVSDG (Tuple Locals Origin)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {m : Model.{u, v, w} Op}

theorem evalFacts_cover (flow : Dataflow Op args past sigs)
    {entryFacts : Tuple (Fact m.value) args} {entry : Tuple (Val m.value) args}
    (hentry : TupleCovers entryFacts entry)
    {facts : Locals (Fact m.value) past} {locals : Locals (Val m.value) past}
    (hlocals : LocalsCover facts locals) :
    LocalsCover (evalFacts m entryFacts flow facts) (flow.eval m entry locals) :=
  Proofs.evalFacts_cover flow hentry hlocals

theorem evalFacts_mono (flow : Dataflow Op args past sigs)
    {lhsArgs rhsArgs : Tuple (Fact m.value) args} (hargs : TupleLE lhsArgs rhsArgs)
    {lhs rhs : Locals (Fact m.value) past} (hlocals : LocalsLE lhs rhs) :
    LocalsLE (evalFacts m lhsArgs flow lhs) (evalFacts m rhsArgs flow rhs) :=
  Proofs.evalFacts_mono flow hargs hlocals

theorem readLocal_mono {t : Ty Data} (wire : Origin args past t)
    {lhsArgs rhsArgs : Tuple (Fact m.value) args} {lhs rhs : Locals (Fact m.value) past}
    (hargs : TupleLE lhsArgs rhsArgs) (hlocals : LocalsLE lhs rhs) :
    readLocal lhsArgs lhs wire ≤ readLocal rhsArgs rhs wire := by
  cases wire with | arg p => exact hargs p | output i p => exact hlocals i p

theorem readLocal_cover {t : Ty Data} (wire : Origin args past t)
    {facts : Tuple (Fact m.value) args} {entry : Tuple (Val m.value) args}
    {abstract : Locals (Fact m.value) past} {locals : Locals (Val m.value) past}
    (hargs : TupleCovers facts entry) (hlocals : LocalsCover abstract locals) :
    (readLocal facts abstract wire).Covers (read m wire entry locals) := by
  cases wire with | arg p => exact hargs p | output i p => exact hlocals i p

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP
