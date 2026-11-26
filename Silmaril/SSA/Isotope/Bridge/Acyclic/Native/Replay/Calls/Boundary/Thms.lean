module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Boundary.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.CallsBoundary

/-! # The computed-call repair and the remaining effectful-pair obstruction -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural Native.CallBoundary

/-- The original two-call witness now replays at its exact typed endpoints. -/
theorem CallBoundary.repaired : nestedEndpoint.CallEqv sequencedEndpoint :=
  repaired_proof

namespace CallPairBoundary

open Region.Paper.BoundSimulation.Obstruction.PairSequencing.CallPair (U Packet left_typed right_typed)
open CallBoundary (input)

/-- Effectful pair sequencing is a valid equation separated by the enlarged relation. -/
theorem separation : paired.Valid sequenced ∧ ¬ paired.CallEqv sequenced :=
  ⟨valid_pair_proof, independent_pair_proof⟩

/-- These exact LetCase derivations use pair eta followed by ordered pair beta. -/
theorem letCase_pair :
    LetCase.LocallyNameless.Equiv false LetCase.Structural.Reply.Γ₀ input
      pairCode.toLetCase.1 seqCode.toLetCase.1 Packet :=
  letCase_pair_proof

/-- Even the exact guarded reifications are distinct in the enlarged relation. -/
theorem reify_pair_fails :
    ¬ Region.Paper.WithComputedCallReturns.ConstructorJoin.Eqv false input.toList
      ((Code.ofLetCase pairCode.toLetCase.2).guardedSSA 0) ((Code.ofLetCase seqCode.toLetCase.2).guardedSSA 0)
      [Packet] :=
  reify_pair_fails_proof

/-- The missing equation is the existing unrestricted ordered pair step. -/
theorem pair_step : Region.Paper.WithPairReturns.Step [U] paired.region sequenced.region [Packet] :=
  .seq left_typed right_typed

end CallPairBoundary
end Silmaril.Isotope.LambdaSSA.Acyclic.Native
