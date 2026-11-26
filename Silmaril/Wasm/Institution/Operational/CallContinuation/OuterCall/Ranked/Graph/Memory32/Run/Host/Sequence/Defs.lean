module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Entry.Defs

/-!
# Checked scalar control leading to direct V1 host sequences

Each selected arm may open more labels or enter a checked host sequence.
Successful delivery places the result above the saved operands and runs the
enclosing continuation with the returned store.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry

open Execution.Runtime (EvalCtx Frame MemAddr MemInst ModuleInst Result Value)
open Computed
open Wasm.V1.Execution

structure HostSegment (H : Type) where
  operands : List Prefix.Op
  site : HostCall.V1.Site H

/-- The root describes the first site and the shared final graph tail. -/
structure Sequence (H : Type) where
  root : HostEntry H
  later : List (HostSegment H)

/-- Source blocks and conditionals along the path to the host sequence.
The zero arm is a checked host-free region. -/
structure PathBlock where
  result : Option NumType
  tail : List Op

structure PathChoice where
  condition : LocalIdx
  alternate : List Op

structure PathNode where
  block : PathBlock
  choice : Option PathChoice := none

/-- Checked block and conditional arms and their enclosing continuations. -/
inductive Source (H : Type) where
  | root
  | hosts (first : HostSegment H) (later : List (HostSegment H))
  | plain (code : List Op)
  | blockThen (result : Option NumType) (body tail : Source H)
  | ifThen (result : Option NumType) (condition : LocalIdx) (left right tail : Source H)

namespace Source

def block {H : Type} (scope : PathBlock) (body : Source H) : Source H :=
  .blockThen scope.result body (.plain scope.tail)

def if_ {H : Type} (scope : PathBlock) (condition : LocalIdx) (left right : Source H) : Source H :=
  .ifThen scope.result condition left right (.plain scope.tail)

def ofPath {H : Type} : List PathNode → Source H
  | [] => .root
  | node :: rest =>
    match node.choice with
    | none => .block node.block (ofPath rest)
    | some test => .if_ node.block test.condition (ofPath rest) (.plain test.alternate)

/-- A plain tail can run in the host-free graph. Other tails must resume at
a source boundary, where the child stack is still typed. -/
def needsResume {H : Type} : Source H → Bool
  | .plain _ => false
  | _ => true

def Allowed {H : Type} (mode : MemoryMode) (program : Program) (memory : MemAddr) (calls : CallMode)
    (fn : Function) : Source H → Prop
  | .root | .hosts .. => True
  | .plain code =>
    CodeAllowedFor mode program memory calls fn.rank fn.declaration.module (expression (v1Code code))
  | .blockThen _ body tail =>
    Allowed mode program memory calls fn tail ∧ Allowed mode program memory calls fn body
  | .ifThen _ _ left right tail =>
    Allowed mode program memory calls fn tail ∧ Allowed mode program memory calls fn left ∧
      Allowed mode program memory calls fn right

end Source

/-- The innermost label comes first. The prefix and tail belong to its parent. -/
structure OpenLabel (H : Type) where
  saved : List Value
  result : Option NumType
  tail : Source H

namespace OpenLabel

variable {H : Type}

def results (fn : Function) (labels : List (OpenLabel H)) : List NumType :=
  (labels.head?.map (fun label => label.result.toList)).getD fn.declaration.results

def targets (fn : Function) (labels : List (OpenLabel H)) : List (List NumType) :=
  labels.map (fun label => label.result.toList) ++ fn.entryLabels

def needsResume (labels : List (OpenLabel H)) : Bool :=
  labels.any (fun label => label.tail.needsResume)

end OpenLabel

namespace Sequence

variable {H : Type}

def first (seq : Sequence H) : HostSegment H :=
  ⟨seq.root.operands, seq.root.site⟩

def sites (seq : Sequence H) : List (HostCall.V1.Site H) :=
  seq.root.site :: seq.later.map HostSegment.site

def encode {A : Type} (ops : ArgumentSyntax A) (tail : List A) : List (HostSegment H) → List A
  | [] => tail
  | segment :: rest =>
    segment.operands.map (Prefix.emit ops) ++ ops.call segment.site.index :: encode ops tail rest

def hostBody (seq : Sequence H) : Wasm.V1.Expr :=
  encode Graph.v1CodeSyntax.ops (v1Code seq.root.function.code) (seq.first :: seq.later)

def sourceCode (seq : Sequence H) : Source H → Wasm.V1.Expr
  | .root => seq.hostBody
  | .hosts first later => encode Graph.v1CodeSyntax.ops (v1Code seq.root.function.code) (first :: later)
  | .plain code => v1Code code
  | .blockThen result body tail => .block result (seq.sourceCode body) :: seq.sourceCode tail
  | .ifThen result condition left right tail =>
    .localGet condition :: .if_ result (seq.sourceCode left) (seq.sourceCode right) :: seq.sourceCode tail

def sourceSites (seq : Sequence H) : Source H → List (HostCall.V1.Site H)
  | .root => seq.sites
  | .hosts first later => first.site :: later.map HostSegment.site
  | .plain _ => []
  | .blockThen _ body tail => seq.sourceSites body ++ seq.sourceSites tail
  | .ifThen _ _ left right tail => (seq.sourceSites left ++ seq.sourceSites right) ++ seq.sourceSites tail

def tailCode (seq : Sequence H) (label : OpenLabel H) : List Admin := expression (seq.sourceCode label.tail)

/-- Insert the innermost administrative label beneath all its parents. -/
def insert (seq : Sequence H) : List (OpenLabel H) → EvalCtx Wasm.V1.Instr
  | [] => .hole
  | label :: rest =>
    (seq.insert rest).comp (.label (OpenLabel.results seq.root.function rest).length []
      (.seq label.saved .hole (seq.tailCode label)))

def context (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H)) : EvalCtx Wasm.V1.Instr :=
  let fn := seq.root.function
  .frame fn.declaration.results.length (fn.declaration.frame args)
    ((seq.insert labels).comp (.label (OpenLabel.results fn labels).length [] .hole))

def v1FuncFor (seq : Sequence H) (body : Source H) : Wasm.V1.Func :=
  let fn := seq.root.function
  ⟨fn.declaration.typeIndex, fn.declaration.locals,
    fn.initial.map Graph.v1CodeSyntax.ops.value ++ seq.sourceCode body⟩

def v1FuncAt (seq : Sequence H) (path : List PathNode) : Wasm.V1.Func :=
  seq.v1FuncFor (Source.ofPath path)

def v1Func (seq : Sequence H) : Wasm.V1.Func := seq.v1FuncFor .root

def continuation (seq : Sequence H) (rest : List (HostSegment H)) : List Admin :=
  encode v1Syntax seq.root.tail rest

/-- Reentering source after label completion requires an exact typed value
stack. The graph guard alone does not provide one after running a graph tail. -/
def checkTail (fn : Function) (stack fallthrough : List NumType) (targets : List (List NumType))
    (resume : Bool) (code : List Op) : Bool :=
  if resume then code.isEmpty && decide (stack = fallthrough.reverse)
  else ({ fn with code := code }).checkRegion stack fallthrough code targets

/-- Consume each ordered argument suffix and check the next segment on its
declared results above the preserved operands. -/
def checkRegionAt (fn : Function) (stack fallthrough : List NumType)
    (targets : List (List NumType)) (resume : Bool) : List (HostSegment H) → Bool
  | [] => checkTail fn stack fallthrough targets resume fn.code
  | segment :: rest =>
    checkHostPrefixWith (fn.declaration.params ++ fn.declaration.locals) stack segment.operands
      segment.site.signature (fun next => checkRegionAt fn next fallthrough targets resume rest)

def checkRegion (fn : Function) (stack fallthrough : List NumType)
    (targets : List (List NumType)) (segments : List (HostSegment H)) : Bool :=
  checkRegionAt fn stack fallthrough targets false segments

def check (fn : Function) (stack : List NumType) (segments : List (HostSegment H)) : Bool :=
  checkRegion fn stack fn.declaration.results fn.entryLabels segments

def checkSourceAt (seq : Sequence H) (stack fallthrough : List NumType) (targets : List (List NumType))
    (resume : Bool) : Source H → Bool
  | .root => checkRegionAt seq.root.function stack fallthrough targets resume (seq.first :: seq.later)
  | .hosts first later => checkRegionAt seq.root.function stack fallthrough targets resume (first :: later)
  | .plain code => checkTail seq.root.function stack fallthrough targets resume code
  | .blockThen result body tail =>
    let types := result.toList
    seq.checkSourceAt (types.reverse ++ stack) fallthrough targets resume tail &&
      seq.checkSourceAt [] types (types :: targets) (tail.needsResume || resume) body
  | .ifThen result condition left right tail =>
    let fn := seq.root.function
    let types := result.toList
    let nested := types :: targets
    let childResume := tail.needsResume || resume
    seq.checkSourceAt (types.reverse ++ stack) fallthrough targets resume tail &&
    (decide ((fn.declaration.params ++ fn.declaration.locals)[condition.toNat]? = some (.int .i32)) &&
      (seq.checkSourceAt [] types nested childResume left && seq.checkSourceAt [] types nested childResume right))

def checkSource (seq : Sequence H) (stack fallthrough : List NumType) (targets : List (List NumType))
    (body : Source H) : Bool :=
  seq.checkSourceAt stack fallthrough targets false body

def checkPath (seq : Sequence H) (stack fallthrough : List NumType) (targets : List (List NumType))
    (path : List PathNode) : Bool :=
  seq.checkSource stack fallthrough targets (Source.ofPath path)

structure Linked (site : HostCall.V1.Site H) (module : ModuleInst) (base : Store H) : Prop where
  resolved : module.funcs[site.index.toNat]? = some site.address
  allocated : base.funcs[site.address.value]? = some (.host site.signature site.target)
  scalar : site.signature.results.length ≤ 1

/-- Admission checks the actual allocated body and all declared host sites.
Host-free execution uses the original guarded Memory32 graph. -/
structure Checked (seq : Sequence H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (base : Store H) (outer : Frame) (args : List Value)
    (body : Source H := .root) : Prop where
  resolved : outer.module.funcs[seq.root.index.toNat]? = some seq.root.address
  allocated : base.funcs[seq.root.address.value]? =
    some (.wasm seq.root.function.declaration.type seq.root.function.declaration.module (seq.v1FuncFor body))
  parameters : args.map Value.type = seq.root.function.declaration.params
  scalar : seq.root.function.declaration.results.length ≤ 1
  slot : seq.root.function.declaration.module.memories[0]? = some memory
  linkedHosts : ∀ site ∈ seq.sourceSites body, Linked site seq.root.function.declaration.module base
  typedBody : seq.checkSource (Prefix.stackTypes seq.root.function.initial) seq.root.function.declaration.results
    seq.root.function.entryLabels body = true
  guardedBody : Source.Allowed mode program memory calls seq.root.function body := by trivial
  supportedTail : supportedCode seq.root.function.code seq.root.function.entryLabels mode
    (program.checkIndirect calls seq.root.function.rank seq.root.function.declaration.module) = true
  linkedTail : ∀ target ∈ seq.root.function.targets,
    ∃ callee, program.lookup target.address = some callee ∧ callee.declaration = target.declaration ∧
      seq.root.function.declaration.module.funcs[target.index.toNat]? = some target.address ∧
      calls.permits seq.root.function.rank callee.rank

/-- The contract is applied at the current live store and actual typed inputs
of each reached site. All returned outcomes, including traps, are covered. -/
def Contract (seq : Sequence H) (host : HostSemantics H) (mode : MemoryMode) (memory : MemAddr)
    (initial : MemInst) (base : Store H) (body : Source H := .root) : Prop :=
  ∀ site ∈ seq.sourceSites body, ∀ bytes, mode.extent initial.data.size bytes →
    ∀ args : List Value, args.map Value.type = site.signature.params →
      site.ReturnContract host (HostStoreEffect mode memory initial) (storeWithBytes base memory initial bytes) args

inductive Phase (H : Type) where
  | call (body : Source H := .root)
  | invoke (body : Source H := .root)
  | block (bytes : ByteArray) (stack : List Value) (result : Option NumType) (body tail : Source H)
      (labels : List (OpenLabel H))
  | if_ (bytes : ByteArray) (stack : List Value) (result : Option NumType) (index : LocalIdx)
      (left right tail : Source H) (labels : List (OpenLabel H))
  | test (bytes : ByteArray) (stack : List Value) (result : Option NumType) (index : LocalIdx)
      (left right tail : Source H) (condition : BitVec 32) (labels : List (OpenLabel H))
  | computing (bytes : ByteArray) (stack : List Value) (remaining : List Prefix.Op)
      (site : HostCall.V1.Site H) (later : List (HostSegment H)) (labels : List (OpenLabel H) := [])
  | pending (bytes : ByteArray) (saved args : List Value)
      (site : HostCall.V1.Site H) (later : List (HostSegment H)) (labels : List (OpenLabel H) := [])
  | completed (bytes : ByteArray) (stack : List Value) (label : OpenLabel H) (outer : List (OpenLabel H))
  | trapped (bytes : ByteArray) (saved : List Value) (tail : List Admin) (labels : List (OpenLabel H) := [])
  | graph (state : State)

def finish (seq : Sequence H) (outer : Frame) (args : List Value) (bytes : ByteArray)
    (stack : List Value) (code : List Op) (labels : List (OpenLabel H)) : Phase H :=
  match labels with
  | [] => .graph ⟨bytes, outer, (seq.context args []).plug value (values stack ++ expression (v1Code code))⟩
  | label :: rest =>
    if OpenLabel.needsResume (label :: rest) && code.isEmpty then .completed bytes stack label rest
    else .graph ⟨bytes, outer, (seq.context args labels).plug value (values stack ++ expression (v1Code code))⟩

def beginBody (seq : Sequence H) (outer : Frame) (args : List Value) (bytes : ByteArray)
    (stack : List Value) (labels : List (OpenLabel H)) : Source H → Phase H
  | .root => .computing bytes stack seq.root.operands seq.root.site seq.later labels
  | .hosts first later => .computing bytes stack first.operands first.site later labels
  | .plain code => seq.finish outer args bytes stack code labels
  | .blockThen result body tail => .block bytes stack result body tail labels
  | .ifThen result index left right tail => .if_ bytes stack result index left right tail labels

def resume (seq : Sequence H) (outer : Frame) (args : List Value) (bytes : ByteArray)
    (stack : List Value) (later : List (HostSegment H)) (labels : List (OpenLabel H) := []) : Phase H :=
  match later with
  | [] => seq.finish outer args bytes stack seq.root.function.code labels
  | piece :: rest => .computing bytes stack piece.operands piece.site rest labels

def delivered (seq : Sequence H) (outer : Frame) (args : List Value) (bytes : ByteArray)
    (saved : List Value) (later : List (HostSegment H)) (r : Result) (labels : List (OpenLabel H) := []) : Phase H :=
  match r with
  | .values payload => seq.resume outer args bytes (saved ++ payload) later labels
  | .trap => .trapped bytes saved (seq.continuation later) labels

def afterLabel (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H))
    (code : List Admin) : List Admin :=
  [.frame seq.root.function.declaration.results.length (seq.root.function.declaration.frame args)
    ((seq.insert labels).plug value code)]

def closeTrapped (seq : Sequence H) (outer : Frame) (args : List Value) (bytes : ByteArray)
    (labels : List (OpenLabel H)) : Phase H :=
  match labels with
  | [] => .graph ⟨bytes, outer, seq.afterLabel args [] [.trap]⟩
  | label :: rest =>
    if OpenLabel.needsResume (label :: rest) then .trapped bytes label.saved (seq.tailCode label) rest
    else .graph ⟨bytes, outer, seq.afterLabel args labels [.trap]⟩

def render (seq : Sequence H) (base : Store H) (memory : MemAddr) (initial : MemInst)
    (start : ByteArray) (outer : Frame) (args : List Value) (phase : Phase H) : Config H :=
  let live bytes := storeWithBytes base memory initial bytes
  let k := seq.context args
  match phase with
  | .call _ => ⟨live start, outer, values args ++ [.source (.call seq.root.index)]⟩
  | .invoke _ => ⟨live start, outer, values args ++ [.invoke seq.root.address]⟩
  | .block bytes stack result body tail labels =>
    ⟨live bytes, outer, (k labels).plug value (values stack ++ expression (seq.sourceCode (.blockThen result body tail)))⟩
  | .if_ bytes stack result index left right tail labels =>
    ⟨live bytes, outer, (k labels).plug value (values stack ++ expression (seq.sourceCode (.ifThen result index left right tail)))⟩
  | .test bytes stack result _ left right tail condition labels =>
    ⟨live bytes, outer, (k labels).plug value (values (stack ++ [Value.int .i32 condition]) ++
      .source (.if_ result (seq.sourceCode left) (seq.sourceCode right)) :: expression (seq.sourceCode tail))⟩
  | .computing bytes stack ops site later labels =>
    ⟨live bytes, outer, (k labels).plug value (values stack ++ ops.map (Prefix.emit v1Syntax) ++
      .source (.call site.index) :: seq.continuation later)⟩
  | .pending bytes saved actual site later labels =>
    ⟨live bytes, outer, (k labels).plug value (values (saved ++ actual) ++ .invoke site.address :: seq.continuation later)⟩
  | .completed bytes stack label rest => ⟨live bytes, outer, (k (label :: rest)).plug value (values stack)⟩
  | .trapped bytes saved tail labels => ⟨live bytes, outer, (k labels).plug value (values saved ++ .trap :: tail)⟩
  | .graph state => Memory32.render base memory initial state

def ContextReady (seq : Sequence H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (body : Source H) : List (OpenLabel H) → Prop
  | [] => True
  | label :: rest =>
    seq.checkSourceAt (label.result.toList.reverse ++ Prefix.stackTypes label.saved)
      (OpenLabel.results seq.root.function rest) (OpenLabel.targets seq.root.function rest) (OpenLabel.needsResume rest) label.tail = true ∧
    Source.Allowed mode program memory calls seq.root.function label.tail ∧
    (∀ site ∈ seq.sourceSites label.tail, site ∈ seq.sourceSites body) ∧
    seq.ContextReady mode program memory calls body rest

def SourceReady (seq : Sequence H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (labels : List (OpenLabel H)) (stack : List Value) (region body : Source H) : Prop :=
  seq.ContextReady mode program memory calls body labels ∧
  Source.Allowed mode program memory calls seq.root.function region ∧
  (∀ site ∈ seq.sourceSites region, site ∈ seq.sourceSites body) ∧
  seq.checkSourceAt (Prefix.stackTypes stack) (OpenLabel.results seq.root.function labels)
    (OpenLabel.targets seq.root.function labels) (OpenLabel.needsResume labels) region = true

/-- Bind the exact arguments, the typed continuations, and the live extent. -/
def Ready (seq : Sequence H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (initial : MemInst) (phase : Phase H) (body : Source H := .root) : Prop :=
  let fn := seq.root.function
  let scopes := seq.ContextReady mode program memory calls body
  let extent := mode.extent initial.data.size
  match phase with
  | .call current | .invoke current => current = body
  | .block bytes stack result region tail labels =>
    extent bytes ∧ seq.SourceReady mode program memory calls labels stack (.blockThen result region tail) body
  | .if_ bytes stack result index left right tail labels | .test bytes stack result index left right tail _ labels =>
    extent bytes ∧ seq.SourceReady mode program memory calls labels stack (.ifThen result index left right tail) body
  | .computing bytes stack ops site later labels =>
    extent bytes ∧ site ∈ seq.sourceSites body ∧
      (∀ piece ∈ later, piece.site ∈ seq.sourceSites body) ∧
      checkHostPrefixWith (fn.declaration.params ++ fn.declaration.locals)
        (Prefix.stackTypes stack) ops site.signature
        (fun next => checkRegionAt fn next (OpenLabel.results fn labels) (OpenLabel.targets fn labels) (OpenLabel.needsResume labels) later) = true ∧
      scopes labels
  | .pending bytes saved actual site later labels =>
    extent bytes ∧ site ∈ seq.sourceSites body ∧
      (∀ piece ∈ later, piece.site ∈ seq.sourceSites body) ∧
      actual.map Value.type = site.signature.params ∧
      checkRegionAt fn (site.signature.results.reverse ++ Prefix.stackTypes saved)
        (OpenLabel.results fn labels) (OpenLabel.targets fn labels) (OpenLabel.needsResume labels) later = true ∧
      scopes labels
  | .completed bytes stack label rest =>
    extent bytes ∧ stack.map Value.type = label.result.toList ∧ scopes (label :: rest)
  | .trapped bytes _ _ labels => extent bytes ∧ scopes labels
  | .graph state => ReadyFor mode program memory calls (fn.rank + 1) initial.data.size state

/-- A step at one of the native entry, prefix, delivery or graph boundaries. -/
inductive Edge (seq : Sequence H) (host : HostSemantics H) (mode : MemoryMode)
    (program : Program) (memory : MemAddr) (base : Store H) (initial : MemInst)
    (start : ByteArray) (outer : Frame) (args : List Value) : Phase H → Phase H → Prop where
  | resolve {body} : Edge seq host mode program memory base initial start outer args (.call body) (.invoke body)
  | enter {body} : Edge seq host mode program memory base initial start outer args (.invoke body)
      (seq.beginBody outer args start seq.root.function.initial [] body)
  | openBlock {bytes stack result region tail labels} :
      Edge seq host mode program memory base initial start outer args (.block bytes stack result region tail labels)
        (seq.beginBody outer args bytes [] (⟨stack, result, tail⟩ :: labels) region)
  | readCondition {bytes stack result index left right tail condition labels}
      (found : (seq.root.function.declaration.frame args).locals[index.toNat]? = some (.int .i32 condition)) :
      Edge seq host mode program memory base initial start outer args
        (.if_ bytes stack result index left right tail labels) (.test bytes stack result index left right tail condition labels)
  | select {bytes stack result index left right tail condition labels} :
      Edge seq host mode program memory base initial start outer args
        (.test bytes stack result index left right tail condition labels)
        (.block bytes stack result (if condition = 0 then right else left) tail labels)
  | closeLabel {bytes stack label rest} (arity : stack.length = label.result.toList.length) :
      Edge seq host mode program memory base initial start outer args (.completed bytes stack label rest)
        (seq.beginBody outer args bytes (label.saved ++ stack) rest label.tail)
  | numeric {bytes stack next op rest site later labels}
      (move : Prefix.Reduce (seq.root.function.declaration.frame args).locals stack op (.values next)) :
      Edge seq host mode program memory base initial start outer args (.computing bytes stack (op :: rest) site later labels)
        (.computing bytes next rest site later labels)
  | prefixTrap {bytes stack saved op rest site later labels}
      (move : Prefix.Reduce (seq.root.function.declaration.frame args).locals stack op (.trap saved)) :
      Edge seq host mode program memory base initial start outer args (.computing bytes stack (op :: rest) site later labels)
        (.trapped bytes saved (rest.map (Prefix.emit v1Syntax) ++ .source (.call site.index) :: seq.continuation later) labels)
  | discard {bytes saved tail kept rest labels} (move : Prefix.Discard saved tail kept rest) :
      Edge seq host mode program memory base initial start outer args (.trapped bytes saved tail labels) (.trapped bytes kept rest labels)
  | closeTrap {bytes labels} :
      Edge seq host mode program memory base initial start outer args (.trapped bytes [] [] labels)
        (seq.closeTrapped outer args bytes labels)
  | hostResolve {bytes saved actual site later labels} (typed : actual.map Value.type = site.signature.params) :
      Edge seq host mode program memory base initial start outer args (.computing bytes (saved ++ actual) [] site later labels)
        (.pending bytes saved actual site later labels)
  | returned {bytes saved actual site later labels after r next}
      (behavior : host site.target (storeWithBytes base memory initial bytes) actual (.returned after r))
      (stored : after = storeWithBytes base memory initial next) :
      Edge seq host mode program memory base initial start outer args (.pending bytes saved actual site later labels)
        (seq.delivered outer args next saved later r labels)
  | diverged {bytes saved actual site later labels}
      (behavior : host site.target (storeWithBytes base memory initial bytes) actual .diverged) :
      Edge seq host mode program memory base initial start outer args (.pending bytes saved actual site later labels)
        (.pending bytes saved actual site later labels)
  | graph {src dst} (move : EdgeAt mode program memory src dst) :
      Edge seq host mode program memory base initial start outer args (.graph src) (.graph dst)

abbrev Runs (seq : Sequence H) (host : HostSemantics H) (mode : MemoryMode)
    (program : Program) (memory : MemAddr) (base : Store H) (initial : MemInst)
    (start : ByteArray) (outer : Frame) (args : List Value) :=
  Relation.ReflTransGen (seq.Edge host mode program memory base initial start outer args)

end Sequence
end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry
