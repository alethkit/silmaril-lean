module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Correctness

/-! # Exact entry, feedback and bounded return agreement -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks

open RVSDG (Port)
open Diamond (Model ValueSort dataPorts)
open SeaOfNodes.Loop (Incoming)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable (p : Program Op regs out) (m : Model.{u, v, w} Op)
variable (input old : Bank (regs := regs) m)

/-- The entry column is the preheader's final reaching-version map. -/
theorem Program.lower_entry_column :
    p.lower.phiInputs .entry = p.entryTransfer.outgoing :=
  rfl

/-- Resolving the pending backedge uses the header's final reaching versions. -/
theorem Program.lower_backedge_column :
    p.lower.phiInputs .backedge = p.headerTransfer.outgoing :=
  rfl

/-- Latching uses the whole bank from the chosen occurrence's single snapshot. -/
theorem Program.latch_agrees (edge : Incoming) :
    p.latch m edge input old = edge.select (p.initial m input) (p.header.body.eval m old) :=
  Proofs.latch_agrees p m input old edge

/-- Each slot in the simultaneous latch agrees on that same occurrence. -/
theorem Program.latch_slot (edge : Incoming) {t : Diamond.Ty Data}
    (port : Port (dataPorts regs) t) :
    (p.latch m edge input old).get port =
      (edge.select (p.initial m input) (p.header.body.eval m old)).get port :=
  congrArg (fun bank => bank.get port) (p.latch_agrees m input old edge)

/-- Entry executes the preheader and latches the bank sent by its jump. -/
theorem Program.lower_initial :
    p.lower.initial m input = p.initial m input :=
  Proofs.lower_initial p m input

/-- Both the updated predicate and the selected observation agree. -/
theorem Program.lower_step :
    p.lower.step m input old = p.step m old :=
  Proofs.lower_step p m input old

theorem Program.lower_evalFrom (budget : Nat) :
    p.lower.evalFrom m input budget old = p.evalFrom m budget old :=
  Proofs.lower_evalFrom p m input old budget

/-- Every backedge budget gives the same return or budget exhaustion from Start. -/
theorem Program.lower_evalBackedges (budget : Nat) :
    p.lower.evalBackedges m budget input = p.evalBackedges m budget input :=
  Proofs.lower_evalBackedges p m input budget

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks
