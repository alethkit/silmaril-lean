module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Proofs

open Diamond (Model Signature Ty Val ValueSort dataPorts)
open RVSDG (Tuple Wires)
open ReturnFold (appendLiteral append_reads read_mapped)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op}

theorem withLiteral_step (g : Graph Op inputs carried entrySigs headerSigs out) (literal : Op [] .predicate)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (old : Tuple (Val m.value) (dataPorts carried)) :
    let args := appendTuple old entry
    let locals := g.header.eval m args PUnit.unit
    (withLiteral g literal).step m entry old =
      if (m.run literal .nil).down then .inr (g.latch m .backedge args locals)
      else .inl (Diamond.read m g.result args locals) := by
  let args := appendTuple old entry
  let added := appendLiteral literal g.header
  let before := g.header.eval m args PUnit.unit
  let after := added.flow.eval m args PUnit.unit
  have reads := append_reads literal g.header args PUnit.unit
  have feedback := read_mapped (g.phiInputs .backedge) (fun _ wire => added.keep wire) args before after reads.1
  change (if (Diamond.read m added.result args after).down then
      Sum.inr (Wires.read ((g.phiInputs .backedge).map (fun _ wire => added.keep wire)) args after)
    else Sum.inl (Diamond.read m (added.keep g.result) args after)) =
    (if (m.run literal .nil).down then Sum.inr ((g.phiInputs .backedge).read args before)
      else Sum.inl (Diamond.read m g.result args before))
  erw [reads.2, feedback, reads.1 _ g.result]

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Proofs
