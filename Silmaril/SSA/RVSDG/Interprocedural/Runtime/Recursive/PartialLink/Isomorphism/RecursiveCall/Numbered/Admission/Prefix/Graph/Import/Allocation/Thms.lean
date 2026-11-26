module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Import.Allocation.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Import.Allocation.Link

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {importsL importsR exports extra : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {providerFn clientFn : Function V S} {value : ValueSort V S}

/-- Admit the client's actual linked export, using the retained provider
dispatch certificate. Unit inequality separates all allocations made by
the provider unit from the client's δ. Clients have one δ and one λ,
with optional empty φ padding. This check assumes the caller manages
allocation identities of any units outside this pair. -/
@[expose] def admitAllocatingClient [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] {captureCode : CaptureCode m} (actions : Actions m σ) {ids : GlobalRel}
    (ordinary : OrdinaryOutputs Op) (exactValue : ExactValueCheck m)
    {providerUnitL providerUnitR : Nat} {providerL : Omega Op importsL exports sigsL}
    {providerR : Omega Op importsR exports sigsR} {providerInputsL : Tuple m.Val importsL}
    {providerInputsR : Tuple m.Val importsR} {port : Port exports providerFn.port} {storeL storeR : σ}
    (provider : CheckedProvider actions ids keys captureCode providerUnitL providerUnitR providerL providerR
      providerInputsL providerInputsR port storeL storeR)
    (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val (providerFn.port :: extra))
    {shiftedL shiftedR : Bool}
    (left : AllocatingClient Op (providerFn.port :: extra) clientFn value shiftedL)
    (right : AllocatingClient Op (providerFn.port :: extra) clientFn value shiftedR) :
    Option (PLift (AdmittedExport actions.toPrimitives ids (fn := clientFn) .head
      (Executable.link actions unitL left.toGraph inputsL provider.checked.storeL)
      (Executable.link actions unitR right.toGraph inputsR provider.checked.storeR) ∧
      unitL ≠ providerUnitL ∧ unitR ≠ providerUnitR)) :=
  if disjoint : unitL ≠ providerUnitL ∧ unitR ≠ providerUnitR then
    let locals := AllocatingClient.initialLocals m
    match ranL : Executable.linkVertex actions unitL inputsL (locals shiftedL)
        (.delta left.initializer) provider.checked.storeL,
      ranR : Executable.linkVertex actions unitR inputsR (locals shiftedR)
        (.delta right.initializer) provider.checked.storeR with
    | .linked valuesL _, .linked valuesR _ => do
      let checked ← provider.checked.addClientLambda ordinary exactValue inputsL inputsR
        ((locals shiftedL).snoc valuesL) ((locals shiftedR).snoc valuesR) left.body right.body
      pure ⟨by
        rw [AllocationProofs.link_body left actions unitL inputsL _,
          AllocationProofs.link_body right actions unitR inputsR _, ranL, ranR]
        exact ⟨checked.down, disjoint⟩⟩
    | _, _ => none
  else none

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix
