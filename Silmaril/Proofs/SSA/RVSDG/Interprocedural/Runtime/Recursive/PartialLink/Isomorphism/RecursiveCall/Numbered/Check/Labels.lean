module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Check.Labels.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Proofs

open NestedTheta.Equality (OpcodeCode)

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}

theorem instructionKey_injective (code : OpcodeCode Op)
    {insL insR outsL outsR : Ports (Ty V S)} {left : Instruction Op insL outsL}
    {right : Instruction Op insR outsR} (sameIn : insL = insR) (sameOut : outsL = outsR)
    (equal : instructionKey code left = instructionKey code right) : HEq left right := by
  cases left with
  | primitive first =>
    cases right with
    | primitive second =>
      subst insR
      subst outsR
      exact heq_of_eq (congrArg Instruction.primitive (code.injective _ _ (Sum.inl.inj equal)))
    | apply => cases equal
  | apply fn =>
    cases right with
    | primitive => cases equal
    | apply other =>
      have ports := Sum.inr.inj equal
      obtain ⟨paramsL, returnsL⟩ := fn
      obtain ⟨paramsR, returnsR⟩ := other
      obtain ⟨sameParams, sameReturns⟩ := Prod.mk.inj ports
      change paramsL = paramsR at sameParams
      change returnsL = returnsR at sameReturns
      subst paramsR
      subst returnsR
      rfl

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Proofs
