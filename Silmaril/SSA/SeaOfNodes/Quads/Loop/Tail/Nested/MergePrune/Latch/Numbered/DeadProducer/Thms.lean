module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Thms

/-! # Exact latch observations and finite returns of the shortened numbered θ -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer

open SeaOfNodes.Diamond (Model ValueSort sortValue)
open Diamond.Prune (HeaderProjection)
open Join (model)
open Nested.Numbered (KeptResult nextBank sourceVisits)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (m : Model.{u, v, w} Op)
variable (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch)
variable (cut : Split.DeadProducer.Checked checked.latchTransfer)

/-- The emitted prefix reads the guard, exit and feedback after the
original γs resolve the selected predecessor. -/
theorem packet_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (packetRegion p projected checked cut).toGraph.run (model m) fuel (carry.project old) =
      some (observe p carry (nextBank p m old)) :=
  Proofs.packet_run m checked cut projected fuel old

/-- The emitted θ body latches the original projected feedback together. -/
theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p projected checked cut).run (model m) fuel (carry.project old) =
      some (MergePrune.Numbered.latchPacket p carry m (nextBank p m old)) :=
  Proofs.activation_run m checked cut projected fuel old

variable (result : KeptResult p (mask := carry)) (input : Bank (regs := regs) m)

theorem lower_run (fuel : Nat) :
    (lower p projected checked cut result).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  Nested.Numbered.lowerWith_run p m _ (activation_run p m projected checked cut) result fuel input

theorem run_agrees (fuel : Nat) :
    (lower p projected checked cut result).run (model m) fuel input =
      (Numbered.lower p projected checked.whole result).run (model m) fuel input :=
  (lower_run p m projected checked cut result input fuel).trans
    (Numbered.lower_run p m projected checked.whole result fuel input).symm

theorem returns_iff (value : sortValue m.value out) :
    (lower p projected checked cut result).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  (exists_congr fun fuel => by rw [run_agrees p m projected checked cut result input fuel]).trans
    (Numbered.returns_iff p m projected checked.whole result input value)

theorem noFiniteReturn_iff :
    (∀ fuel, (lower p projected checked cut result).run (model m) fuel input = none) ↔
      ∀ fuel, src.runFrom m fuel entry input = none := by
  refine ⟨fun h fuel => Option.eq_none_iff_forall_ne_some.mpr (fun value found => ?_),
    fun h fuel => by rw [lower_run, h]; rfl⟩
  obtain ⟨bound, returned⟩ := (returns_iff p m projected checked cut result input value).2 ⟨fuel, found⟩
  exact Option.eq_none_iff_forall_ne_some.mp (h bound) _ returned

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer
