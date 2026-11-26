module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg)
open Silmaril.MLIR.Pure (Operands)
open Header.Earlier (operations)
open Header.Sequence (State)
open Loop.MLIR.CF (Program TargetOp evalOp lower)

variable {Input Γ : List Width} {saved carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {first : AfterReorder.Plan} {consumerOrigin : Nat} {prepared : Prepared Input carried result}

/-- The handoff retains the exact intermediate CFG and resolves its current origin order. -/
theorem prepareOn?_spec {intermediate : Output Input carried result} {origins : List Nat}
    (accepted : prepareOn? intermediate origins consumerOrigin = some prepared) :
    prepared.intermediate = intermediate ∧ prepared.origins = origins ∧
    prepared.origins.idxOf? consumerOrigin = some prepared.index ∧
    findCandidate? prepared.index 0 savedOrigins (prepared.intermediate.2.block .header) =
      some prepared.consumer ∧ checkConsumer prepared.intermediate.2 prepared.consumer = true :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepareOn?_spec accepted

/-- The first hoist removes exactly its resolved operation from header order. -/
theorem hoistCodeWith?_operations
    {entry : Block TargetOp (SourceLabel carried result) Input [result]}
    {header : Block TargetOp (SourceLabel carried result) (carried :: Input) [result]}
    {choose : List (Point (SourceLabel carried result)) → List (Use (SourceLabel carried result)) →
      Option (Point (SourceLabel carried result))}
    {index : Nat} {cut : Point (SourceLabel carried result)} {output : Output Input carried result}
    (moved : hoistCodeWith? entry header index choose = some (cut, output)) :
    operations (output.2.block .header) = (operations header).eraseIdx index :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.hoistCodeWith?_operations moved

/-- The captured operands evaluate the current typed binding in a header activation. -/
theorem findCandidate?_value {index cut : Nat}
    {origins : Origins (saved :: Input) Γ} {code : Block TargetOp (Label saved carried result) Γ [result]}
    {candidate : Candidate Input saved carried result}
    (found : findCandidate? index cut origins code = some candidate)
    (env : Env Γ) (inputs : Env (saved :: Input)) (agree : CapturesAgree origins env inputs) :
    valueAt? index code env = some ⟨candidate.width, evalOp candidate.op (candidate.inputs.eval inputs)⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.findCandidate?_value
    found env inputs agree

/-- The intermediate CFG is exactly the first hoist's replay result. -/
theorem prepare?_replay_first (accepted : prepare? g first consumerOrigin = some prepared) :
    AfterReorder.replay? g first = some prepared.intermediate :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepare?_replay_first accepted

/-- Removal transports the origin table to the actual intermediate header,
and the consumer's definition and use sites admit preheader cut one. -/
theorem prepare?_placement (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ (state : State Input carried result) (firstIndex : Nat),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      state.origins[firstIndex]? = some first.hoistOrigin ∧
      prepared.origins = state.origins.eraseIdx firstIndex ∧
      prepared.origins[prepared.index]? = some consumerOrigin ∧
      prepared.origins.map (fun origin => (operations ((lower g).block .header))[origin]?) =
        (operations (prepared.intermediate.2.block .header)).map some ∧
      findCandidate? prepared.index 0 savedOrigins (prepared.intermediate.2.block .header) =
        some prepared.consumer ∧
      Legal prepared.intermediate.2 prepared.consumer.operands prepared.consumer.uses ⟨none, 1⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepare?_placement accepted

/-- Immediately after the first preheader binding, the consumer can be
evaluated from the resulting value and immutable inputs for any latch. -/
theorem prepare?_available (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      ∀ (input : Env Input) (old : BitVec carried.val),
        let saved := evalOp producer (operands.eval input)
        valueAt? prepared.index (prepared.intermediate.2.block .header) (.cons saved (.cons old input)) =
          some ⟨prepared.consumer.width, evalOp prepared.consumer.op
            (prepared.consumer.inputs.eval (.cons saved input))⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepare?_available accepted

/-- The leading preheader let computes the exact value supplied by the first
emitter on entry and feedback. The exit block is the canonical return. -/
theorem prepare?_first_routes (accepted : prepare? g first consumerOrigin = some prepared)
    (input : Env Input) :
    ∃ (source : Cfg TargetOp (SourceLabel carried result) Input [result])
      (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      prepared.intermediate.2.block .exit = .terminator (.ret (.cons .here .nil)) ∧
      Routes source prepared.intermediate.2 input (evalOp producer (operands.eval input)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepare?_first_routes accepted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
