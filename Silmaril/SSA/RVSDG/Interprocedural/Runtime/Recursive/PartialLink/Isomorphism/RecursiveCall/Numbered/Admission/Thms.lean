module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Groups

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Continuation.Partial (Config Primitives)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args outs : Ports (Ty V S)} {primitives : Primitives m σ}

theorem checkExport_sound [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)} [DecidableEq keys.Key]
    (ordinary : OrdinaryOutputs Op) {left right : m.Val (.value (.function args outs))}
    (accepted : checkExport keys left right = true) : ExportAdmission primitives ids left right :=
  AdmissionProofs.checkExport_sound ordinary accepted

/-- Produce closed-family evidence from the checked linked origins and the
dialect's output restriction. Primitive compatibility is a separate premise
when using the resulting family to compare runs. -/
@[expose] def admitExport [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (primitives : Primitives m σ) (ids : GlobalRel) (ordinary : OrdinaryOutputs Op)
    (left right : m.Val (.value (.function args outs))) : Option (PLift (ExportAdmission primitives ids left right)) :=
  if accepted : checkExport keys left right = true then some ⟨checkExport_sound ordinary accepted⟩ else none

/-- Use the selected values from the partial linker's related success
outcomes. The roots retain the exact arguments and the common post-link store. -/
theorem ExportAdmission.atExport {exports : Ports (Ty V S)} {valuesL valuesR : Tuple m.Val exports}
    (port : Port exports (.value (.function args outs))) {store : σ} {rename : Nat → Nat}
    (linked : OutcomesRelated m ids σ rename exports (.linked valuesL store) (.linked valuesR store))
    (checked : ExportAdmission primitives ids (valuesL.get port) (valuesR.get port))
    {inputL inputR : Tuple m.Val args} (inputs : TupleRelated m ids inputL inputR)
    (ordinary : ordinaryPorts args = true) :
    ∃ familyL familyR, ClosedFamily primitives ids familyL familyR ∧
      Admitted m ids familyL familyR
        (⟨Continuation.start (.call (valuesL.get port) inputL), store⟩ : Config m σ outs)
        ⟨Continuation.start (.call (valuesR.get port) inputR), store⟩ := by
  obtain ⟨left, right, family, calleeL, calleeR, plain⟩ := checked
  cases linked with | linked values =>
    exact ⟨left, right, family.toClosed, .call (values.get port) inputs calleeL calleeR
      (plain inputL ordinary).1 (plain inputR ordinary).2 store⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered
