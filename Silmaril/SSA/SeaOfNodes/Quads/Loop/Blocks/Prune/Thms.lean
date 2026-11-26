module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Correctness

/-! # Projection and exact return agreement for a validated carried bank -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune

open Diamond (Dataflow Model Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Port Tuple Wires)
open SeaOfNodes.Loop (appendTuple)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
section Projection

variable (mask : Mask regs) {past sigs : List (List (Ty Data))}

theorem Mask.project_get {F : Ty Data → Type w} (bank : Tuple F (dataPorts regs))
    {t : Ty Data} (port : Port (dataPorts regs) t) (kept : Port (dataPorts mask.kept) t)
    (h : mask.rename port = some kept) : (mask.project bank).get kept = bank.get port :=
  Proofs.project_get mask bank port kept h

variable (m : Model.{u, v, w} Op)

theorem Mask.project_read {args : List (Ty Data)} (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) (wires : Wires args past (dataPorts regs)) :
    Wires.read (mask.project wires) entry locals = mask.project (wires.read entry locals) :=
  Proofs.project_read mask m entry locals wires

theorem Mask.projected_flow (bank : Tuple (Val m.value) (dataPorts regs))
    (locals : Locals (Val m.value) past) (flow : Dataflow Op (dataPorts regs) past sigs)
    (mapped : Dataflow Op (dataPorts mask.kept) past sigs)
    (h : renameFlow mask.rename flow = some mapped) :
    mapped.eval m (mask.project bank) locals = flow.eval m bank locals :=
  Proofs.projected_flow mask m bank locals flow mapped h

theorem Mask.projected_wires (bank : Tuple (Val m.value) (dataPorts regs))
    (locals : Locals (Val m.value) past) {outs : List (Ty Data)}
    (wires : Wires (dataPorts regs) past outs) (mapped : Wires (dataPorts mask.kept) past outs)
    (h : renameWires mask.rename wires = some mapped) :
    mapped.read (mask.project bank) locals = wires.read bank locals :=
  Proofs.projected_wires mask m bank locals wires mapped h

end Projection

variable (p : Program Op regs out) (mask : Mask regs) {g : PrunedGraph p mask}
variable (accepted : pruneWith p mask = some g)
include accepted

/-- The typed carried signature is strictly smaller whenever pruning succeeds. -/
theorem smaller : mask.kept.length < regs.length :=
  Proofs.smaller p mask accepted

variable (m : Model.{u, v, w} Op) (input old : Bank (regs := regs) m)

/-- Entry latches the projection of the source preheader's final bank. -/
theorem initial_agrees :
    g.initial m input = mask.project (p.initial m input) :=
  (Proofs.simulate p mask accepted m input input).1

/-- Feedback simultaneously latches the projection of the source header's
updated bank from the same activation. -/
theorem feedback_agrees :
    let args := appendTuple (mask.project old) input
    g.latch m .backedge args (g.header.eval m args PUnit.unit) =
      mask.project (p.header.body.eval m old) :=
  (Proofs.simulate p mask accepted m input old).2.1

/-- Control and returns agree exactly. Continuing projects the next latch. -/
theorem step_agrees :
    g.step m input (mask.project old) = (p.step m old).map id mask.project :=
  (Proofs.simulate p mask accepted m input old).2.2

theorem evalFrom_agrees (budget : Nat) :
    g.evalFrom m input budget (mask.project old) = p.evalFrom m budget old :=
  Proofs.evalFrom_agrees p mask accepted m input old budget

/-- All budgets preserve both exhaustion and the returned value. -/
theorem eval_agrees (budget : Nat) :
    g.evalBackedges m budget input = p.evalBackedges m budget input :=
  Proofs.eval_agrees p mask accepted m input budget

/-- A target finite return is exactly a successful source observation at
some backedge budget. -/
theorem returns_iff (result : sortValue m.value out) :
    g.Returns m input result ↔ ∃ budget, p.evalBackedges m budget input = some result :=
  Proofs.returns_iff p mask accepted m input result

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune
