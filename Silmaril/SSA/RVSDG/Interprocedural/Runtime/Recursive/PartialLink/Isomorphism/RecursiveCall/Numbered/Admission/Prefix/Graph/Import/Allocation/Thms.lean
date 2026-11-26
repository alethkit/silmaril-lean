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

/-- Compose successful link traces at their common boundary store. -/
theorem AllocationHistory.append {actions : Actions m σ} {unitsA unitsB : List Nat}
    {start middle final : σ} (first : AllocationHistory actions unitsA start middle)
    (second : AllocationHistory actions unitsB middle final) :
    AllocationHistory actions (unitsB ++ unitsA) start final := by
  induction second with
  | empty => exact first
  | link _ ran ih => exact .link (ih first) ran

/-- A reusable checked link result and the unit namespaces reserved by
the links that produced it, most recent first. Reservations cover those
links' allocations. Globals from opaque imports are outside this history. -/
structure CheckedAllocationChain (actions : Actions m σ) (ids : GlobalRel)
    (keys : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m)
    (unitsL unitsR : List Nat) (port : Port exports providerFn.port)
    (outcomeL outcomeR : Outcome m σ exports) where
  private mk ::
  checked : CheckedExport actions.toPrimitives ids keys captureCode port outcomeL outcomeR
  initialL : σ
  initialR : σ
  historyL : AllocationHistory actions unitsL initialL checked.storeL
  historyR : AllocationHistory actions unitsR initialR checked.storeR
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
  CheckedAllocationChain.mk provider.checked storeL storeR
    (.link (.empty storeL) provider.checked.linkedL) (.link (.empty storeR) provider.checked.linkedR)
    (List.nodup_singleton _) (List.nodup_singleton _)

/-- The newest allocation unit is fresh against every earlier unit on its side. -/
theorem CheckedAllocationChain.fresh {actions : Actions m σ} {ids : GlobalRel}
    {keys : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
    {unitsL unitsR : List Nat} {unitL unitR : Nat} {port : Port exports providerFn.port}
    {outcomeL outcomeR : Outcome m σ exports}
    (chain : CheckedAllocationChain actions ids keys captureCode (unitL :: unitsL) (unitR :: unitsR) port outcomeL outcomeR) :
    unitL ∉ unitsL ∧ unitR ∉ unitsR :=
  ⟨(List.nodup_cons.mp chain.nodupL).1, (List.nodup_cons.mp chain.nodupR).1⟩

private def extendWithImports [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] {captureCode : CaptureCode m} (actions : Actions m σ) {ids : GlobalRel}
    (ordinary : OrdinaryOutputs Op)
    {familyL familyR : Family m} {dispatch : DispatchKeys V S keys.Key captureCode.Key}
    (prior : LinkedFamily actions.toPrimitives ids keys captureCode familyL familyR dispatch)
    {unitsL unitsR : List Nat} (nodupL : unitsL.Nodup) (nodupR : unitsR.Nodup)
    {initialL initialR storeL storeR : σ}
    (historyL : AllocationHistory actions unitsL initialL storeL)
    (historyR : AllocationHistory actions unitsR initialR storeR)
    (unitL unitR : Nat) {imports : Ports (Ty V S)} (inputsL inputsR : Tuple m.Val imports)
    (rowL : Row familyL inputsL) (rowR : Row familyR inputsR)
    {shiftedL shiftedR : Bool}
    (left : AllocatingClient Op imports clientFn value shiftedL)
    (right : AllocatingClient Op imports clientFn value shiftedR) :
    Option (CheckedAllocationChain actions ids keys captureCode (unitL :: unitsL) (unitR :: unitsR)
      (providerFn := clientFn) .head
      (Executable.link actions unitL left.toGraph inputsL storeL)
      (Executable.link actions unitR right.toGraph inputsR storeR)) :=
  if fresh : unitL ∉ unitsL ∧ unitR ∉ unitsR then
    let locals := AllocatingClient.initialLocals m
    match ranL : Executable.linkVertex actions unitL inputsL (locals shiftedL)
        (.delta left.initializer) storeL,
      ranR : Executable.linkVertex actions unitR inputsR (locals shiftedR)
        (.delta right.initializer) storeR with
    | .linked valuesL finalL, .linked valuesR finalR => do
      let scopeL := (locals shiftedL).snoc valuesL
      let scopeR := (locals shiftedR).snoc valuesR
      let some certified := prior.addLambda keys ordinary
        ((Table.empty familyL scopeL).availableWithImports prior.ordinaryL rowL)
        ((Table.empty familyR scopeR).availableWithImports prior.ordinaryR rowR) left.body right.body | none
      let calleeL := linkedLambda left.body inputsL scopeL
      let calleeR := linkedLambda right.body inputsR scopeR
      have linkedL : Executable.link actions unitL left.toGraph inputsL storeL =
          .linked (.cons calleeL .nil) finalL := by
        rw [AllocationProofs.link_body, ranL]
      have linkedR : Executable.link actions unitR right.toGraph inputsR storeR =
          .linked (.cons calleeR .nil) finalR := by
        rw [AllocationProofs.link_body, ranR]
      pure (CheckedAllocationChain.mk
        ⟨WithExport familyL calleeL, WithExport familyR calleeR,
          _, certified.down, .cons calleeL .nil, .cons calleeR .nil, finalL, finalR, linkedL, linkedR,
          WithExport.exported, WithExport.exported⟩
        initialL initialR
        (.link historyL linkedL) (.link historyR linkedR)
        (List.nodup_cons.mpr ⟨fresh.1, nodupL⟩) (List.nodup_cons.mpr ⟨fresh.2, nodupR⟩))
    | _, _ => none
  else none

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
      (Executable.link actions unitR right.toGraph inputsR prior.checked.storeR)) := do
  let some known := prior.checked.checkImport exactValue (inputsL.get .head) (inputsR.get .head) | none
  extendWithImports actions ordinary prior.checked.certified prior.nodupL prior.nodupR
    prior.historyL prior.historyR unitL unitR inputsL inputsR
    (Row.headOnly known.down.1) (Row.headOnly known.down.2) left right

section Join

variable {actions : Actions m σ} {ids : GlobalRel} {keys : OpcodeCode (Instruction Op)}
variable {captureCode : CaptureCode m}
variable {exportsA exportsB : Ports (Ty V S)} {fnA fnB : Function V S}
variable {unitsAL unitsAR unitsBL unitsBR : List Nat}
variable {portA : Port exportsA fnA.port} {portB : Port exportsB fnB.port}
variable {aL aR : Outcome m σ exportsA} {bL bR : Outcome m σ exportsB}

/-- Two checked histories in link order. The second starts at exactly the
first's final stores. Every reserved unit is disjoint from the other
history's units on its side. The dispatch union retains both families. -/
structure CheckedProviderJoin
    (first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR)
    (second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR) : Type where
  orderedL : second.initialL = first.checked.storeL
  orderedR : second.initialR = first.checked.storeR
  distinctL : (unitsBL ++ unitsAL).Nodup
  distinctR : (unitsBR ++ unitsAR).Nodup
  certified : LinkedFamily actions.toPrimitives ids keys captureCode
    (UnionIn first.checked.familyL second.checked.familyL) (UnionIn first.checked.familyR second.checked.familyR)
    (first.checked.keys.append second.checked.keys)

theorem CheckedProviderJoin.historyL
    {first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR}
    {second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR}
    (joined : CheckedProviderJoin first second) :
    AllocationHistory actions (unitsBL ++ unitsAL) first.initialL second.checked.storeL :=
  first.historyL.append (joined.orderedL ▸ second.historyL)

theorem CheckedProviderJoin.historyR
    {first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR}
    {second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR}
    (joined : CheckedProviderJoin first second) :
    AllocationHistory actions (unitsBR ++ unitsAR) first.initialR second.checked.storeR :=
  first.historyR.append (joined.orderedR ▸ second.historyR)

/-- Reconcile two receipts by checking the store boundary, allocation
history and both mixed dispatch directions. Neither link runs again. -/
def CheckedAllocationChain.join [DecidableEq (Ty V S)] [DecidableEq keys.Key] [DecidableEq σ]
    (first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR)
    (second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR)
    (ordinary : OrdinaryOutputs Op) : Option (CheckedProviderJoin first second) :=
  if order : second.initialL = first.checked.storeL ∧ second.initialR = first.checked.storeR then
    if distinct : (unitsBL ++ unitsAL).Nodup ∧ (unitsBR ++ unitsAR).Nodup then
      (first.checked.certified.join ordinary second.checked.certified).map fun union =>
        ⟨order.1, order.2, distinct.1, distinct.2, union.down⟩
    else none
  else none

private def twoImports {family : Family m} {inputs : Tuple m.Val (fnA.port :: fnB.port :: extra)}
    (knownA : family (inputs.get .head)) (knownB : family (inputs.get (.tail .head))) : Row family inputs
  | _, .head => some ⟨knownA⟩
  | _, .tail .head => some ⟨knownB⟩
  | _, .tail (.tail _) => none

/-- Link a δ→λ client at the second history's final stores. The first two
imports must be the exact exports of the two providers in order. Additional
captures may use the ordinary-value rule. Opaque allocations lie outside
the two certified reservation histories. -/
def CheckedProviderJoin.extend [DecidableEq (Ty V S)] [DecidableEq keys.Key]
    {first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR}
    {second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR}
    (joined : CheckedProviderJoin first second) (ordinary : OrdinaryOutputs Op) (exactValue : ExactValueCheck m)
    (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val (fnA.port :: fnB.port :: extra))
    {shiftedL shiftedR : Bool}
    (left : AllocatingClient Op (fnA.port :: fnB.port :: extra) clientFn value shiftedL)
    (right : AllocatingClient Op (fnA.port :: fnB.port :: extra) clientFn value shiftedR) :
    Option (CheckedAllocationChain actions ids keys captureCode (unitL :: (unitsBL ++ unitsAL))
      (unitR :: (unitsBR ++ unitsAR)) (providerFn := clientFn) .head
      (Executable.link actions unitL left.toGraph inputsL second.checked.storeL)
      (Executable.link actions unitR right.toGraph inputsR second.checked.storeR)) := do
  let some knownA := first.checked.checkImport exactValue (inputsL.get .head) (inputsR.get .head) | none
  let some knownB := second.checked.checkImport exactValue (inputsL.get (.tail .head)) (inputsR.get (.tail .head)) | none
  extendWithImports actions ordinary joined.certified joined.distinctL joined.distinctR
    joined.historyL joined.historyR unitL unitR inputsL inputsR
    (twoImports (Or.inl knownA.down.1) (Or.inr knownB.down.1))
    (twoImports (Or.inl knownA.down.2) (Or.inr knownB.down.2)) left right

end Join

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
