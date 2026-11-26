module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Defs
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Proofs

open RVSDG (Port Tuple)
open Diamond (Model ValueSort dataPorts)
open Join (Block)
open SeaOfNodes.Loop (Graph Incoming appendTuple)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable (p : Program Op regs out) (m : Model.{u, v, w} Op)
variable (input old : Bank (regs := regs) m)

theorem lower_initial : p.lower.initial m input = p.initial m input :=
  (CFG.compileBlock_read (past := []) p.preheader.body m input PUnit.unit (initial regs)).trans
    (congrArg (Block.eval p.preheader.body m) (read_initial m input))

private theorem header_agrees :
    let args := appendTuple old input
    p.headerTransfer.outgoing.read args (p.headerTransfer.flow.eval m args PUnit.unit) =
      p.header.body.eval m old :=
  (CFG.compileBlock_read (past := []) p.header.body m (appendTuple old input) PUnit.unit
    (headerVersions regs)).trans
    (congrArg (Block.eval p.header.body m) (header_read m input old))

theorem latch_agrees (edge : Incoming) :
    p.latch m edge input old = edge.select (p.initial m input) (p.header.body.eval m old) := by
  cases edge with
  | entry => exact lower_initial p m input
  | backedge => exact header_agrees p m input old

theorem lower_step : p.lower.step m input old = p.step m old := by
  let args := appendTuple old input
  let locals := p.headerTransfer.flow.eval m args PUnit.unit
  have bank : p.headerTransfer.outgoing.read args locals = p.header.body.eval m old :=
    header_agrees p m input old
  have port_agrees {t : Diamond.Ty Data} (port : Port (dataPorts regs) t) :
      Diamond.read m (p.headerTransfer.outgoing.get port) args locals =
        (p.header.body.eval m old).get port :=
    (read_get m p.headerTransfer.outgoing args locals port).symm.trans
      (congrArg (fun bank => bank.get port) bank)
  change (if (Diamond.read m (p.headerTransfer.outgoing.get p.header.test) args locals).down
    then Sum.inr (p.headerTransfer.outgoing.read args locals)
    else Sum.inl (Diamond.read m (p.headerTransfer.outgoing.get p.header.result) args locals)) = _
  rw [port_agrees, port_agrees, bank]
  rfl

theorem lower_evalFrom (budget : Nat) :
    p.lower.evalFrom m input budget old = p.evalFrom m budget old := by
  induction budget generalizing old with
  | zero =>
    rw [Graph.evalFrom, Program.evalFrom, lower_step]
    rfl
  | succ budget ih =>
    rw [Graph.evalFrom, Program.evalFrom, lower_step]
    cases p.step m old with
    | inl _ => rfl
    | inr next => exact ih next

theorem lower_evalBackedges (budget : Nat) :
    p.lower.evalBackedges m budget input = p.evalBackedges m budget input :=
  (lower_evalFrom p m input (p.lower.initial m input) budget).trans
    (congrArg (p.evalFrom m budget) (lower_initial p m input))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Proofs
