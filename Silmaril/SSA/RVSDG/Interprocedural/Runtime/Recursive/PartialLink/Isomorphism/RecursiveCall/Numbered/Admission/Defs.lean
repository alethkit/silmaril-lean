module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Infer.Defs

/-! Admission for standalone λ exports and fixed φ member groups. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Continuation.Partial (Primitives)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {args outs : Ports (Ty V S)}

/-- Ordinary ports do not contain callable values, including inside a global. -/
def ordinarySort : ValueSort V S → Bool
  | .data _ => true
  | .function _ _ => false
  | .global value => ordinarySort value

def ordinaryPort : Ty V S → Bool
  | .value value => ordinarySort value
  | .control _ | .state _ => true

abbrev ordinaryPorts (ports : Ports (Ty V S)) : Bool := ports.all ordinaryPort

/-- A conservative primitive interface. The runtime may read callables,
but each successful primitive output consists entirely of ordinary ports. -/
def OrdinaryOutputs (Op : Dialect.{u, v} (ValueSort V S) S) : Prop :=
  ∀ {input output : Ports (Ty V S)}, Op input output → ordinaryPorts output = true

/-- The exact outer capture tuple and definition table stored by a linked
member. The family includes every fixed slot of this group. -/
structure Group (m : Machine.{u, v, w} Op) (members : List (Function V S)) where
  context : Ports (Ty V S)
  values : Tuple m.Val context
  definitions : MemberTable Op context members

def Group.ref {members : List (Function V S)} (group : Group m members)
    (slot : Fin members.length) : m.Val members[slot].port :=
  .member group.values group.definitions slot

inductive Group.In {members : List (Function V S)} (group : Group m members) : Family m where
  | ordinary {port : Ty V S} (value : m.Val port) (plain : ordinaryPort port = true) : Group.In group value
  | member (slot : Fin members.length) : Group.In group (group.ref slot)

/-- A standalone family admits ordinary values and one exact callable.
The capture check is separate from membership in this family. -/
inductive StandaloneIn (root : m.Val (.value (.function args outs))) : Family m where
  | ordinary {port : Ty V S} (value : m.Val port) (plain : ordinaryPort port = true) : StandaloneIn root value
  | exported : StandaloneIn root root

def isStandaloneLambda {port : Ty V S} : m.Val port → Bool
  | .closure _ _ => true
  | _ => false

/-- Admission for the actual export values. All ordinary entry arguments
are admitted. Callable values obtained by following internal wires stay
within their respective families, including across recursive calls. -/
def ExportAdmission (primitives : Primitives m σ) (ids : GlobalRel)
    (left right : m.Val (.value (.function args outs))) : Prop :=
  ∃ familyL familyR, CheckedFamily primitives ids familyL familyR ∧ familyL left ∧ familyR right ∧
    (∀ {ports : Ports (Ty V S)} (values : Tuple m.Val ports), ordinaryPorts ports = true →
      TupleIn familyL values ∧ TupleIn familyR values)

/-- Recover the actual group and a proof that the export belongs to it. -/
structure ExportGroup {port : Ty V S} (value : m.Val port) where
  members : List (Function V S)
  group : Group m members
  known : group.In value

def exportGroup : {port : Ty V S} → (value : m.Val port) → Option (ExportGroup value)
  | _, .member (members := members) values definitions slot =>
    some ⟨members, ⟨_, values, definitions⟩, .member slot⟩
  | _, _ => none

variable [DecidableEq (Ty V S)]

/-- Check all slots, including members that are reachable by recursion but
are absent from the module's export list. Each body comes from resolving
a real linked value with its actual captures. -/
def checkGroups (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    {members : List (Function V S)} (left right : Group m members) : Bool :=
  ordinaryPorts left.context && ordinaryPorts right.context &&
    (List.ofFn (fun slot : Fin members.length =>
      (inferResolved keys (resolve m (left.ref slot)) (resolve m (right.ref slot))).isSome)).all id

/-- Select the finite families directly from two actual exported values.
The checker accepts paired standalone λ closures or paired φ exports
with ordinary outer captures. Paired invocation also uses linker
provenance and compatible primitives. -/
def checkExport (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (left right : m.Val (.value (.function args outs))) : Bool :=
  if isStandaloneLambda left && isStandaloneLambda right then
    let bodyL := resolve m left
    let bodyR := resolve m right
    ordinaryPorts bodyL.context && ordinaryPorts bodyR.context && (inferResolved keys bodyL bodyR).isSome
  else
    letI : DecidableEq (Function V S) := fun a b =>
      decidable_of_iff (a.args = b.args ∧ a.results = b.results) (by cases a; cases b; simp)
    match exportGroup left, exportGroup right with
    | some left, some right =>
      if same : left.members = right.members then
        checkGroups keys left.group (same.symm ▸ right.group)
      else false
    | _, _ => false

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered
