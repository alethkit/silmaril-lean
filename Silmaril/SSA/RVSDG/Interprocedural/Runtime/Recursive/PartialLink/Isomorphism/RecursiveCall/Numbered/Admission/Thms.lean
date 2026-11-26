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

theorem LinkedFamily.ofGroups_sound [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] (ordinary : OrdinaryOutputs Op) {membersL membersR : List (Function V S)}
    (left : Group m membersL) (right : Group m membersR) (accepted : checkGroupPair keys left right = true) :
    LinkedFamily primitives ids left.In right.In [] :=
  AdmissionProofs.linked_groups ordinary left right accepted

/-- Seed ordered admission from the actual tables of two earlier linked
φ groups. Their fixed recursive slots stay within those tables. -/
@[expose] def LinkedFamily.ofGroups [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (primitives : Primitives m σ) (ids : GlobalRel) (ordinary : OrdinaryOutputs Op)
    {membersL membersR : List (Function V S)} (left : Group m membersL) (right : Group m membersR) :
    Option (PLift (LinkedFamily primitives ids left.In right.In [])) :=
  if accepted : checkGroupPair keys left right = true then some ⟨ofGroups_sound ordinary left right accepted⟩ else none

theorem LinkedFamily.extend (ordinary : OrdinaryOutputs Op)
    {familyL familyR : Family m} {prior : List (LambdaKey V S)}
    (earlier : LinkedFamily primitives ids familyL familyR prior)
    {left right : m.Val (.value (.function args outs))}
    {key : LambdaKey V S} (fresh : key ∉ prior)
    (keyL : lambdaKey left = some key) (keyR : lambdaKey right = some key)
    (capturesL : TupleIn familyL (resolve m left).values) (capturesR : TupleIn familyR (resolve m right).values)
    (body : Resolved m ⟨args, outs⟩ (resolve m left) (resolve m right)) :
    LinkedFamily primitives ids (WithExport familyL left) (WithExport familyR right) (key :: prior) :=
  AdmissionProofs.linked_extension ordinary earlier fresh keyL keyR capturesL capturesR body

theorem Resolved.context_eq {fn : Function V S} {left right : Closure Op m.Val fn}
    (checked : Resolved m fn left right) : left.context = right.context := by
  cases checked
  rfl

/-- Extend an already checked prefix by one pair of λ definitions. Capture
evidence comes from their typed wires into the actual prefix. The key
disjointness check conservatively rules out mixed dispatch to a previously
added λ with the same signature and ordered capture types. -/
@[expose] def LinkedFamily.addLambda [DecidableEq (Ty V S)]
    (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] (ordinary : OrdinaryOutputs Op)
    {familyL familyR : Family m} {prior : List (LambdaKey V S)}
    (earlier : LinkedFamily primitives ids familyL familyR prior)
    {importsL importsR : Ports (Ty V S)} {pastL pastR : List (Ports (Ty V S))} {fn : Function V S}
    {entryL : Tuple m.Val importsL} {entryR : Tuple m.Val importsR}
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (availableL : Available familyL entryL localsL) (availableR : Available familyR entryR localsR)
    (left : Lambda Op importsL pastL fn) (right : Lambda Op importsR pastR fn) :
    Option (PLift (LinkedFamily primitives ids (WithExport familyL (linkedLambda left entryL localsL))
      (WithExport familyR (linkedLambda right entryR localsR)) ((fn.args, fn.results, left.context) :: prior))) :=
  if fresh : (fn.args, fn.results, left.context) ∉ prior then do
    let capturesL ← checkWires availableL left.captures
    let capturesR ← checkWires availableR right.captures
    let body ← inferResolved keys (resolve m (linkedLambda left entryL localsL))
      (resolve m (linkedLambda right entryR localsR))
    have context : left.context = right.context := body.down.context_eq
    have keyR : lambdaKey (linkedLambda right entryR localsR) = some (fn.args, fn.results, left.context) :=
      congrArg (fun ports => some (fn.args, fn.results, ports)) context.symm
    pure ⟨earlier.extend ordinary fresh rfl keyR capturesL.down capturesR.down body.down⟩
  else none

theorem LinkedFamily.addLambda_accepts [DecidableEq (Ty V S)]
    (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] (ordinary : OrdinaryOutputs Op)
    {familyL familyR : Family m} {prior : List (LambdaKey V S)}
    (earlier : LinkedFamily primitives ids familyL familyR prior)
    {importsL importsR : Ports (Ty V S)} {pastL pastR : List (Ports (Ty V S))} {fn : Function V S}
    {entryL : Tuple m.Val importsL} {entryR : Tuple m.Val importsR}
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (availableL : Available familyL entryL localsL) (availableR : Available familyR entryR localsR)
    (left : Lambda Op importsL pastL fn) (right : Lambda Op importsR pastR fn)
    (fresh : (fn.args, fn.results, left.context) ∉ prior)
    (capturesL : (checkWires availableL left.captures).isSome = true)
    (capturesR : (checkWires availableR right.captures).isSome = true)
    (body : (inferResolved keys (resolve m (linkedLambda left entryL localsL))
      (resolve m (linkedLambda right entryR localsR))).isSome = true) :
    (earlier.addLambda keys ordinary availableL availableR left right).isSome = true := by
  obtain ⟨_, capL⟩ := Option.isSome_iff_exists.mp capturesL
  obtain ⟨_, capR⟩ := Option.isSome_iff_exists.mp capturesR
  obtain ⟨_, inferred⟩ := Option.isSome_iff_exists.mp body
  simp [addLambda, fresh, capL, capR, inferred]

theorem LinkedFamily.forExports {familyL familyR : Family m} {prior : List (LambdaKey V S)}
    (family : LinkedFamily primitives ids familyL familyR prior)
    {left right : m.Val (.value (.function args outs))}
    (knownL : familyL left) (knownR : familyR right) : ExportAdmission primitives ids left right :=
  AdmissionProofs.linked_exports family knownL knownR

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
