module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Thms
import Silmaril.SSA.PEG.Bridge.RVSDG.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Proofs

open RVSDG (Port Tuple)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)
open RVSDG.LambdaSSA.Theta
open Isotope (Value)
open Isotope.LambdaSSA.Semantics.Region (Eval)

universe u

variable {Data : Type} {P : InstructionSet.{0,0} Data} {σ : Type u}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried result} {allowInvariant : Bool}
variable (b : Bundle g slot allowInvariant) (m : TotalModel P)
variable (input : Tuple m.toPEG.Value carried)

/-- Every finite target execution has the same ordered defined PEG result,
with the unique external exit and unchanged ambient state, and conversely. -/
theorem lower_eval_iff
    (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (idx : Index 1) (start finish : σ) (label : Nat) (payload : Value (Operational.Atom (Region.model m))) :
    Eval (Operational.instruction (Region.model m))
      (Operational.inputEnv (Region.model m) (encode m input)) (lower b) start label payload finish ↔
      ∃ output : Tuple m.toPEG.Value carried,
        g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) ∧
        label = 0 ∧ payload = Operational.pack (Region.model m) (encode m output) ∧ finish = start := by
  let rt := Region.model m
  rw [lower, Operational.lower_eval_iff]
  constructor
  · rintro ⟨packed, ran, exit, same, state⟩
    let output := fromPorts (F := rt.Val) carried packed
    have round : encode m output = packed := to_fromPorts packed
    exact ⟨output, (b.returns_iff_observe m input neg idx output).mp (round.symm ▸ ran),
      exit, same.trans (congrArg (Operational.pack rt) round.symm), state⟩
  · rintro ⟨output, observed, exit, same, state⟩
    exact ⟨encode m output, (b.returns_iff_observe m input neg idx output).mpr observed, exit, same, state⟩

/-- A finite CFG evaluation recovers the common PEG pass count and all
defined eval prefixes from the single checked loop trace. -/
theorem firstExit_of_eval
    (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (idx : Index 1) (output : Tuple m.toPEG.Value carried) (state : σ)
    (ran : Eval (Operational.instruction (Region.model m))
      (Operational.inputEnv (Region.model m) (encode m input)) (lower b)
      state 0 (Operational.pack (Region.model m) (encode m output)) state) :
    ∃ (k : Nat) (final : Tuple m.toPEG.Value (.bool :: carried)),
      carriedValues final = output ∧
      b.scalar.TraceObservation m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx k final := by
  obtain ⟨packed, returned, _, packetEq, _⟩ :=
    (Operational.lower_eval_iff (Region.model m) b.compile (encode m input) state state 0 _).mp ran
  have same := Operational.pack_injective (Region.model m) packetEq
  have exactReturn : b.compile.Returns (Region.model m) (encode m input) (encode m output) :=
    same.symm ▸ returned
  obtain ⟨k, _, final, _, _, resultEq, exit, _⟩ := b.firstExit_of_returns m input neg idx output exactReturn
  exact ⟨k, final, resultEq, exit⟩

/-- The bounded runner finds the Figure 11 tuple exactly when a sufficiently
large finite bound exists. Fuel exhaustion is a bounded outcome. -/
theorem exists_runFuel_iff_observe
    (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (idx : Index 1) (output : Tuple m.toPEG.Value carried) :
    (∃ fuel, runFuel b m fuel input = some output) ↔
      g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) := by
  rw [← b.returns_iff_observe m input neg idx, Operational.returns_iff_runFuel]
  constructor
  · rintro ⟨fuel, ran⟩
    obtain ⟨packed, executed, decoded⟩ := Option.map_eq_some_iff.mp ran
    exact ⟨fuel, executed.trans (congrArg some ((to_fromPorts packed).symm.trans (congrArg (encode m) decoded)))⟩
  · rintro ⟨fuel, ran⟩
    exact ⟨fuel, Option.map_eq_some_iff.mpr ⟨_, ran, from_toPorts (F := (Region.model m).Val) output⟩⟩

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Proofs
