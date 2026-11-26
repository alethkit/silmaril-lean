module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Correctness

/-! # Checked reaching versions and exact native loop observations -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain

open Diamond (Model Ty ValueSort dataPorts sortValue)
open RVSDG (Wires)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {header site entry : Fin size}

/-- Compiling the scheduled activation gives the same typed map as passing
the outgoing versions across each original jump in order. -/
theorem Path.outgoing_eq {args : List (Ty Data)} {past : List (List (Ty Data))}
    (path : Path src header site) (current : Wires args past (dataPorts regs)) :
    (CFG.compileBlock path.quads current).outgoing = path.outgoing current :=
  Proofs.outgoing_eq path current

variable (p : Program src entry)

/-- The original source occurrences of the entry and feedback columns are
distinct even when the activation consists of one tested header. -/
theorem Program.predecessor_distinct : p.predecessor .entry ≠ p.predecessor .backedge := by
  intro same
  change entry = p.activation.latchBlock at same
  exact (List.nodup_cons.mp p.distinct).1 (by
    simpa only [← same] using Proofs.latch_mem p.activation)

/-- The entry selects the preheader's outgoing versions from the initialized bank. -/
theorem Program.entry_column : p.lower.phiInputs .entry = p.fuse.entryTransfer.outgoing := rfl

/-- The true latch occurrence feeds the final reaching versions into the
pending header arguments. The full tuple is resolved in one old activation. -/
theorem Program.feedback_column : p.lower.phiInputs .backedge = p.feedbackColumn :=
  p.activation.outgoing_eq (headerVersions regs)

variable (m : Model.{u, v, w} Op) (input : Bank (regs := regs) m)

/-- One entry visit and one whole activation are needed for the first
return. Every completed backedge adds another activation's worth of
source visits. A surplus shorter than one activation cannot affect results. -/
theorem Program.lower_budget (budget extra : Nat) (short : extra < p.activationLength) :
    src.runFrom m (extra + p.activationLength * (budget + 1) + 1) entry input =
      p.lower.evalBackedges m budget input :=
  Proofs.lower_budget m p input budget extra short

/-- Exact agreement for every source fuel, including exhaustion both before
the first test and between successive tests. -/
theorem Program.lower_run (fuel : Nat) :
    src.runFrom m fuel entry input =
      if p.activationLength + 1 ≤ fuel then
        p.lower.evalBackedges m ((fuel - (p.activationLength + 1)) / p.activationLength) input
      else none :=
  Proofs.lower_run m p input fuel

/-- Successful source evaluation at some budget is exactly a finite native return. -/
theorem Program.returns_iff (result : sortValue m.value out) :
    p.lower.Returns m input result ↔ ∃ fuel, src.runFrom m fuel entry input = some result :=
  Proofs.returns_iff m p input result

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain
