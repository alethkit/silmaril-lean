module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Infer.Defs
public import Mathlib.Data.Multiset.Defs

/-! Admission for λ exports and fixed φ member groups. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Continuation.Partial (Primitives)
open NestedTheta.Equality (KindCode OpcodeCode kindCode)

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

/-- Extend a callable family with an exact exported value. For the checked
capture case the earlier family is the fixed group captured by the λ. -/
inductive WithExport (earlier : Family m) (root : m.Val (.value (.function args outs))) : Family m where
  | inherited {port : Ty V S} {value : m.Val port} (known : earlier value) : WithExport earlier root value
  | exported : WithExport earlier root root

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

def memberSlot {port : Ty V S} : m.Val port → Option Nat
  | .member _ _ slot => some slot.val
  | _ => none

/-- This capture policy admits a single direct member among ordinary
captures. It records membership in that member's actual linked group. -/
inductive GroupCaptures {members : List (Function V S)} (group : Group m members) :
    {ports : Ports (Ty V S)} → Tuple m.Val ports → Prop where
  | member {port : Ty V S} {ports : Ports (Ty V S)} {value : m.Val port} {rest : Tuple m.Val ports}
      (known : group.In value) (plain : ordinaryPorts ports = true) : GroupCaptures group (.cons value rest)
  | ordinary {port : Ty V S} {ports : Ports (Ty V S)} {value : m.Val port} {rest : Tuple m.Val ports}
      (plain : ordinaryPort port = true) (captures : GroupCaptures group rest) : GroupCaptures group (.cons value rest)

structure CapturedGroup {ports : Ports (Ty V S)} (values : Tuple m.Val ports) where
  members : List (Function V S)
  group : Group m members
  slot : Option Nat
  captures : GroupCaptures group values

/-- Extract the actual captured member and its definition table. Ordinary
captures before or after it are admitted by their port types. -/
def capturedGroup : {ports : Ports (Ty V S)} → (values : Tuple m.Val ports) → Option (CapturedGroup values)
  | _, .nil => none
  | _, .cons (t := port) (ts := ports) value rest =>
    if ordinary : ordinaryPort port = true then
      (capturedGroup rest).map fun found => ⟨found.members, found.group, found.slot, .ordinary ordinary found.captures⟩
    else if plain : ordinaryPorts ports = true then
      (exportGroup value).map fun found => ⟨found.members, found.group, memberSlot value, .member found.known plain⟩
    else none

/-- A numbered vertex contributes its ordered operand and result types
and the code of its kind, including the opcode for primitives and applies. -/
abbrev LabelCode (V S : Type u) (Key : Type v) := Ports (Ty V S) × Ports (Ty V S) × KindCode Key

def labelCode (code : OpcodeCode (Instruction Op)) (label : NestedTheta.NodeLabel (Instruction Op)) :
    LabelCode V S code.Key :=
  (label.ins, label.outs, kindCode code label.kind)

def outerLabels (code : OpcodeCode (Instruction Op)) {sigs : List (Ports (Ty V S))}
    (body : Graph Op args [] sigs outs) : List (LabelCode V S code.Key) :=
  List.ofFn fun i => labelCode code (body.nodes i).label

/-- The multiset of outer vertex labels forgets numbering. The ordered
body checker still verifies execution order. -/
def outerProfile (code : OpcodeCode (Instruction Op)) {sigs : List (Ports (Ty V S))}
    (body : Graph Op args [] sigs outs) : Multiset (LabelCode V S code.Key) :=
  Multiset.ofList (outerLabels code body)

abbrev LambdaSummary (V S : Type u) (Key : Type v) :=
  Ports (Ty V S) × Ports (Ty V S) × Ports (Ty V S) × Multiset (LabelCode V S Key)

/-- Keep the labels as a list for the executable permutation check. -/
structure LambdaKey (V S : Type u) (Key : Type v) where
  args : Ports (Ty V S)
  results : Ports (Ty V S)
  context : Ports (Ty V S)
  labels : List (LabelCode V S Key)

def LambdaKey.summary {Key : Type v} (key : LambdaKey V S Key) : LambdaSummary V S Key :=
  (key.args, key.results, key.context, Multiset.ofList key.labels)

def LambdaKey.Fresh {Key : Type v} (key : LambdaKey V S Key) (prior : List (LambdaKey V S Key)) : Prop :=
  key.summary ∉ prior.map LambdaKey.summary

instance [DecidableEq (Ty V S)] {Key : Type v} [DecidableEq Key]
    (key : LambdaKey V S Key) (prior : List (LambdaKey V S Key)) : Decidable (key.Fresh prior) :=
  letI : DecidableEq (Ports (Ty V S)) := inferInstance
  letI : DecidableEq (LabelCode V S Key) := inferInstance
  decidable_of_iff (prior.any (fun old => decide
    (key.args = old.args ∧ key.results = old.results ∧ key.context = old.context ∧
      key.labels.Perm old.labels)) = false) (by
    simp only [List.any_eq_false, decide_eq_true_eq, LambdaKey.Fresh, List.mem_map, not_exists, not_and]
    exact forall_congr' fun old => by
      rw [eq_comm (a := old.summary) (b := key.summary)]
      simp only [LambdaKey.summary, Prod.mk.injEq, Multiset.coe_eq_coe, not_and])

def lambdaKey (code : OpcodeCode (Instruction Op)) {port : Ty V S} :
    m.Val port → Option (LambdaSummary V S code.Key)
  | .closure (params := params) (results := results) (context := context) _ body =>
    some (params, results, context, outerProfile code body)
  | _ => none

def lambdaBodyKey (code : OpcodeCode (Instruction Op)) {imports : Ports (Ty V S)}
    {past : List (Ports (Ty V S))} {fn : Function V S} (definition : Lambda Op imports past fn) :
    LambdaKey V S code.Key :=
  ⟨fn.args, fn.results, definition.context, outerLabels code definition.body⟩

/-- Empty γ rows can be skipped by ordered admission independently on
either side, so retain the actual profiles of each side. -/
structure LambdaKeys (V S : Type u) (Key : Type v) where
  left : List (LambdaKey V S Key)
  right : List (LambdaKey V S Key)

/-- A checked finite prefix, indexed by the encoder used throughout its
λ keys. Fixed φ members do not have λ keys. -/
structure LinkedFamily (primitives : Primitives m σ) (ids : GlobalRel)
    (code : OpcodeCode (Instruction Op)) (left right : Family m)
    (keys : LambdaKeys V S code.Key) : Prop where
  checked : CheckedFamily primitives ids left right
  ordinaryL : ∀ {port : Ty V S} (value : m.Val port), ordinaryPort port = true → left value
  ordinaryR : ∀ {port : Ty V S} (value : m.Val port), ordinaryPort port = true → right value
  keysL : ∀ {port : Ty V S} {value : m.Val port} {key : LambdaSummary V S code.Key},
    left value → lambdaKey code value = some key → key ∈ keys.left.map LambdaKey.summary
  keysR : ∀ {port : Ty V S} {value : m.Val port} {key : LambdaSummary V S code.Key},
    right value → lambdaKey code value = some key → key ∈ keys.right.map LambdaKey.summary

variable {imports : Ports (Ty V S)} {past : List (Ports (Ty V S))}

/-- Evidence offered for the actual value of a typed origin in a link
prefix. An unchecked origin has no membership certificate. -/
abbrev Available (family : Family m) (entry : Tuple m.Val imports) (locals : Locals m.Val past) :=
  ∀ {port : Ty V S} (origin : Origin imports past port),
    Option (PLift (family ((Wires.read (.cons origin .nil) entry locals).get .head)))

/-- Read the definition's real capture wires and collect the exact
membership evidence from the already checked binding positions. -/
def checkWires {family : Family m} {entry : Tuple m.Val imports} {locals : Locals m.Val past}
    (available : Available family entry locals) :
    {ports : Ports (Ty V S)} → (wires : Wires imports past ports) →
    Option (PLift (TupleIn family (wires.read entry locals)))
  | _, .nil => some ⟨trivial⟩
  | _, .cons origin rest => do
    let head ← available origin
    let tail ← checkWires available rest
    pure ⟨⟨head.down, tail.down⟩⟩

/-- The exact closure returned by linking a λ binding. -/
abbrev linkedLambda {fn : Function V S} (definition : Lambda Op imports past fn)
    (entry : Tuple m.Val imports) (locals : Locals m.Val past) : m.Val fn.port :=
  (lambdaValue m entry locals definition).get .head

variable [DecidableEq (Ty V S)]

/-- Check all slots, including members that are reachable by recursion but
are absent from the module's export list. Each body comes from resolving
a real linked value with its actual captures. -/
def checkGroups (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    {members : List (Function V S)} (left right : Group m members) : Bool :=
  ordinaryPorts left.context && ordinaryPorts right.context &&
    (List.ofFn (fun slot : Fin members.length =>
      (inferResolved keys (resolve m (left.ref slot)) (resolve m (right.ref slot))).isSome)).all id

/-- Compare the exact member signatures in slot order before using the
common table-indexed checker. -/
def checkGroupPair (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    {membersL membersR : List (Function V S)} (left : Group m membersL) (right : Group m membersR) : Bool :=
  letI : DecidableEq (Function V S) := fun a b =>
    decidable_of_iff (a.args = b.args ∧ a.results = b.results) (by cases a; cases b; simp)
  if same : membersL = membersR then checkGroups keys left (same.symm ▸ right) else false

def checkCapturedGroups (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    {portsL portsR : Ports (Ty V S)} (left : Tuple m.Val portsL) (right : Tuple m.Val portsR) : Bool :=
  match capturedGroup left, capturedGroup right with
  | some left, some right => left.slot == right.slot && checkGroupPair keys left.group right.group
  | _, _ => false

/-- Select the finite families directly from two actual exported values.
Paired λ closures admit ordinary captures or one matched φ member each.
The φ groups must have ordinary outer captures. Paired invocation also
uses linker provenance and compatible primitives. -/
def checkExport (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (left right : m.Val (.value (.function args outs))) : Bool :=
  if isStandaloneLambda left && isStandaloneLambda right then
    let bodyL := resolve m left
    let bodyR := resolve m right
    (ordinaryPorts bodyL.context && ordinaryPorts bodyR.context ||
      checkCapturedGroups keys bodyL.values bodyR.values) && (inferResolved keys bodyL bodyR).isSome
  else
    match exportGroup left, exportGroup right with
    | some left, some right => checkGroupPair keys left.group right.group
    | _, _ => false

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered
