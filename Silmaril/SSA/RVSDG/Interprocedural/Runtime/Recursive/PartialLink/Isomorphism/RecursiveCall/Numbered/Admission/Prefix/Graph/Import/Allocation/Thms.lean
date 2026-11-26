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

/-- A reusable checked link result and the unit namespaces reserved by
the links that produced it, most recent first. Reservations cover those
links' allocations. Globals from opaque imports are outside this history. -/
structure CheckedAllocationChain (actions : Actions m σ) (ids : GlobalRel)
    (keys : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m)
    (unitsL unitsR : List Nat) (port : Port exports providerFn.port)
    (outcomeL outcomeR : Outcome m σ exports) where
  private mk ::
  checked : CheckedExport actions.toPrimitives ids keys captureCode port outcomeL outcomeR
  nodupL : unitsL.Nodup
  nodupR : unitsR.Nodup

/-- Reserve the units of the actual provider links. -/
def CheckedProvider.allocationChain {actions : Actions m σ} {ids : GlobalRel}
    {keys : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
    {unitL unitR : Nat} {left : Omega Op importsL exports sigsL} {right : Omega Op importsR exports sigsR}
    {inputsL : Tuple m.Val importsL} {inputsR : Tuple m.Val importsR}
    {port : Port exports providerFn.port} {storeL storeR : σ}
    (provider : CheckedProvider actions ids keys captureCode unitL unitR left right inputsL inputsR port storeL storeR) :
    CheckedAllocationChain actions ids keys captureCode [unitL] [unitR] port
      (Executable.link actions unitL left inputsL storeL) (Executable.link actions unitR right inputsR storeR) :=
  CheckedAllocationChain.mk provider.checked (List.nodup_singleton _) (List.nodup_singleton _)

/-- The newest allocation unit is fresh against every earlier unit on its side. -/
theorem CheckedAllocationChain.fresh {actions : Actions m σ} {ids : GlobalRel}
    {keys : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
    {unitsL unitsR : List Nat} {unitL unitR : Nat} {port : Port exports providerFn.port}
    {outcomeL outcomeR : Outcome m σ exports}
    (chain : CheckedAllocationChain actions ids keys captureCode (unitL :: unitsL) (unitR :: unitsR) port outcomeL outcomeR) :
    unitL ∉ unitsL ∧ unitR ∉ unitsR :=
  ⟨(List.nodup_cons.mp chain.nodupL).1, (List.nodup_cons.mp chain.nodupR).1⟩

/-- Link the client at the previous link's exact store. A successful
extension retains the new dispatch family and reserves the new unit against
the entire checked history on each side. -/
def CheckedAllocationChain.extend [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] {captureCode : CaptureCode m} (actions : Actions m σ) {ids : GlobalRel}
    (ordinary : OrdinaryOutputs Op) (exactValue : ExactValueCheck m)
    {unitsL unitsR : List Nat} {port : Port exports providerFn.port} {outcomeL outcomeR : Outcome m σ exports}
    (prior : CheckedAllocationChain actions ids keys captureCode unitsL unitsR port outcomeL outcomeR)
    (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val (providerFn.port :: extra))
    {shiftedL shiftedR : Bool}
    (left : AllocatingClient Op (providerFn.port :: extra) clientFn value shiftedL)
    (right : AllocatingClient Op (providerFn.port :: extra) clientFn value shiftedR) :
    Option (CheckedAllocationChain actions ids keys captureCode (unitL :: unitsL) (unitR :: unitsR)
      (providerFn := clientFn) .head
      (Executable.link actions unitL left.toGraph inputsL prior.checked.storeL)
      (Executable.link actions unitR right.toGraph inputsR prior.checked.storeR)) :=
  if fresh : unitL ∉ unitsL ∧ unitR ∉ unitsR then
    let locals := AllocatingClient.initialLocals m
    match ranL : Executable.linkVertex actions unitL inputsL (locals shiftedL)
        (.delta left.initializer) prior.checked.storeL,
      ranR : Executable.linkVertex actions unitR inputsR (locals shiftedR)
        (.delta right.initializer) prior.checked.storeR with
    | .linked valuesL storeL, .linked valuesR storeR => do
      let scopeL := (locals shiftedL).snoc valuesL
      let scopeR := (locals shiftedR).snoc valuesR
      let some certified := prior.checked.extendClientLambda ordinary exactValue inputsL inputsR
        scopeL scopeR left.body right.body | none
      let calleeL := linkedLambda left.body inputsL scopeL
      let calleeR := linkedLambda right.body inputsR scopeR
      have linkedL : Executable.link actions unitL left.toGraph inputsL prior.checked.storeL =
          .linked (.cons calleeL .nil) storeL := by
        rw [AllocationProofs.link_body, ranL]
      have linkedR : Executable.link actions unitR right.toGraph inputsR prior.checked.storeR =
          .linked (.cons calleeR .nil) storeR := by
        rw [AllocationProofs.link_body, ranR]
      pure (CheckedAllocationChain.mk
        ⟨WithExport prior.checked.familyL calleeL, WithExport prior.checked.familyR calleeR,
          _, certified.down, .cons calleeL .nil, .cons calleeR .nil, storeL, storeR, linkedL, linkedR,
          WithExport.exported, WithExport.exported⟩
        (List.nodup_cons.mpr ⟨fresh.1, prior.nodupL⟩) (List.nodup_cons.mpr ⟨fresh.2, prior.nodupR⟩))
    | _, _ => none
  else none

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
  (provider.allocationChain.extend actions ordinary exactValue unitL unitR inputsL inputsR left right).map fun next =>
    ⟨by simpa only [CheckedProvider.allocationChain] using next.checked.admitted, fun equal => next.fresh.1 (equal.symm ▸ List.mem_cons_self),
      fun equal => next.fresh.2 (equal.symm ▸ List.mem_cons_self)⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix
