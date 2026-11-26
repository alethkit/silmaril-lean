module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi

universe v w
variable {V K α : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]
variable {source : Graph V K F} {lexical : CFG (Option V × Nat) (Option K) F}

theorem continue_mem_iff (lowered : compile source = some lexical)
    (model : Model F Part α) (pairs : model.PairLawful) (input : V → α)
    (current : Pending V K α) (jump : Option K × α) :
    Sum.inr jump ∈ Cyclic.stepSSA model lexical.blocks (inputEnv model input)
        (encode model source current) ↔
      ∃ next, Sum.inr next ∈ step model source current ∧ encode model source next = jump := by
  rw [← step_commutes lowered model pairs input current, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨result, ran, encoded⟩
    cases result with
    | inl _ => cases encoded
    | inr next => exact ⟨next, ran, Sum.inr.inj encoded⟩
  · rintro ⟨next, ran, rfl⟩
    exact ⟨.inr next, ran, rfl⟩

end Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi
