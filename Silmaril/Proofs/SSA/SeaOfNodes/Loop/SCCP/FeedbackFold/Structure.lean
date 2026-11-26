module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Proofs

open Diamond (Model Signature Ty Val ValueSort dataPorts)
open RVSDG (Origin Port Tuple Wires extend)
open ReturnFold (appendLiteral append_reads read_mapped)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out sort : ValueSort Data}
variable {m : Model.{u, v, w} Op}

theorem write_get {T : Type u} {F : T → Type w} {ports : List T} {t : T}
    (port : Port ports t) (values : Tuple F ports) : Quads.write port (values.get port) values = values := by
  induction port with
  | head => cases values; rfl
  | tail _ ih =>
    cases values with
    | cons value tail => exact congrArg (Tuple.cons value) (ih tail)

theorem withLiteral_step (g : Graph Op inputs carried entrySigs headerSigs out)
    (port : Port (dataPorts carried) (.value sort)) (literal : Op [] sort)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (old : Tuple (Val m.value) (dataPorts carried)) :
    (withLiteral g port literal).step m entry old =
      (g.step m entry old).map id (Quads.write port (m.run literal .nil)) := by
  let args := appendTuple old entry
  let added := appendLiteral literal g.header
  let before := g.header.eval m args PUnit.unit
  let after := added.flow.eval m args PUnit.unit
  let kept := (g.phiInputs .backedge).map (fun _ wire => added.keep wire)
  have reads := append_reads literal g.header args PUnit.unit
  let readWire (t : Ty Data)
      (wire : Origin (headerPorts inputs carried) (extend [] (headerSigs ++ [[.value sort]])) t) :
      Val m.value t := Diamond.read m wire args after
  have mapWrite := Quads.map_write readWire port added.result kept
  have writes : Wires.read (Quads.write port added.result kept) args after =
      Quads.write port (Diamond.read m added.result args after) (Wires.read kept args after) :=
    mapWrite
  have feedback := read_mapped (g.phiInputs .backedge) (fun _ wire => added.keep wire) args before after reads.1
  change (if (Diamond.read m (added.keep g.predicate) args after).down then
      Sum.inr (Wires.read (Quads.write port added.result kept) args after)
    else Sum.inl (Diamond.read m (added.keep g.result) args after)) =
    (if (Diamond.read m g.predicate args before).down then
      Sum.inr ((g.phiInputs .backedge).read args before)
    else Sum.inl (Diamond.read m g.result args before)).map id (Quads.write port (m.run literal .nil))
  erw [reads.1 _ g.predicate, reads.1 _ g.result, writes, reads.2, feedback]
  split <;> rfl

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Proofs
