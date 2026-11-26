module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Correctness

/-! # Projection and exact return agreement for a validated carried bank -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune

open Diamond (Model ValueSort sortValue)
open SeaOfNodes.Loop (appendTuple)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
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
