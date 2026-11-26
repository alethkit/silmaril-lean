module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Infinite.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.Infinite

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi

universe v w
variable {V K α : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]
variable {source : Graph V K F} {lexical : CFG (Option V × Nat) (Option K) F}

/-- A successful lexical entry packet has a successful source entry as its preimage. -/
theorem entry_mem_iff (lowered : compile source = some lexical)
    (model : Model F Part α) (pairs : model.PairLawful) (input : V → α) (jump : Option K × α) :
    jump ∈ lexical.entry.evalJump model (inputEnv model input) ↔
      ∃ pending, pending ∈ execute model none source.entry input ∧ encode model source pending = jump := by
  rw [← entry_commutes lowered model pairs input, Part.map_eq_map, Part.mem_map_iff]

/-- From a related current transfer, successful lexical continuations are exactly
the packet encodings of successful source continuations. The preimage retains
the predecessor and store used by the next φ transfer. -/
theorem continue_mem_iff (lowered : compile source = some lexical)
    (model : Model F Part α) (pairs : model.PairLawful) (input : V → α)
    (current : Pending V K α) (jump : Option K × α) :
    Sum.inr jump ∈ Cyclic.stepSSA model lexical.blocks (inputEnv model input)
        (encode model source current) ↔
      ∃ next, Sum.inr next ∈ step model source current ∧ encode model source next = jump :=
  Proofs.SSA.LambdaRTL.CFG.CyclicPhi.continue_mem_iff lowered model pairs input current jump

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi
