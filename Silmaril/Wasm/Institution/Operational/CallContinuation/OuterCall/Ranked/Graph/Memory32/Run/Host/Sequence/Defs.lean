module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Entry.Defs

/-!
# A finite straight-line sequence of direct V1 host sites

Each site follows a checked numeric prefix in the same activation. Successful
delivery places the result above the saved operands and checks the remaining
sites on that stack. The existing Memory32 graph handles the final tail.
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

/-- Entered labels are innermost first. The operand prefix and continuation
belong to the enclosing region, while the result belongs to this label. -/
structure OpenLabel where
  saved : List Value
  block : PathBlock

namespace OpenLabel

def results (fn : Function) (labels : List OpenLabel) : List NumType :=
  (labels.head?.map (fun label => label.block.result.toList)).getD fn.declaration.results

def targets (fn : Function) (labels : List OpenLabel) : List (List NumType) :=
  labels.map (fun label => label.block.result.toList) ++ fn.entryLabels

def tail (label : OpenLabel) : List Admin := expression (v1Code label.block.tail)

def checkTail (fn : Function) (stack : List NumType) (fallthrough : List NumType)
    (targets : List (List NumType)) (code : List Op) : Bool :=
  ({ fn with code := code }).checkRegion stack fallthrough code targets

def Typed (fn : Function) : List OpenLabel → Prop
  | [] => True
  | label :: rest =>
    checkTail fn (label.block.result.toList.reverse ++ Prefix.stackTypes label.saved)
      (results fn rest) (targets fn rest) label.block.tail = true ∧ Typed fn rest

def Allowed (mode : MemoryMode) (program : Program) (memory : MemAddr) (calls : CallMode)
    (fn : Function) (labels : List OpenLabel) : Prop :=
  ∀ label ∈ labels, CodeAllowedFor mode program memory calls fn.rank fn.declaration.module label.tail

/-- Insert the innermost administrative label in each enclosing label
sequence. The innermost label can later be replaced by its delivered code. -/
def insert (fn : Function) : List OpenLabel → EvalCtx Wasm.V1.Instr
  | [] => .hole
  | label :: rest =>
    (insert fn rest).comp (.label (results fn rest).length [] (.seq label.saved .hole label.tail))

def context (fn : Function) (args : List Value) (labels : List OpenLabel) : EvalCtx Wasm.V1.Instr :=
  .frame fn.declaration.results.length (fn.declaration.frame args)
    ((insert fn labels).comp (.label (results fn labels).length [] .hole))

end OpenLabel

namespace PathNode

def emit (node : PathNode) (inside : Wasm.V1.Expr) : Wasm.V1.Expr :=
  match node.choice with
  | none => .block node.block.result inside :: v1Code node.block.tail
  | some test =>
    .localGet test.condition :: .if_ node.block.result inside (v1Code test.alternate) :: v1Code node.block.tail

def Allowed (mode : MemoryMode) (program : Program) (memory : MemAddr) (calls : CallMode)
    (fn : Function) : List PathNode → Prop
  | [] => True
  | node :: rest =>
    CodeAllowedFor mode program memory calls fn.rank fn.declaration.module (expression (v1Code node.block.tail)) ∧
    (∀ test ∈ node.choice, ∀ instr ∈ v1Code test.alternate,
      SourceAllowedFor mode program memory calls fn.rank fn.declaration.module instr) ∧
    Allowed mode program memory calls fn rest

end PathNode

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

def sourcePath (seq : Sequence H) (path : List PathNode) : Wasm.V1.Expr :=
  path.foldr PathNode.emit seq.hostBody

def v1FuncAt (seq : Sequence H) (path : List PathNode) : Wasm.V1.Func :=
  let fn := seq.root.function
  ⟨fn.declaration.typeIndex, fn.declaration.locals,
    fn.initial.map Graph.v1CodeSyntax.ops.value ++ seq.sourcePath path⟩

def v1Func (seq : Sequence H) : Wasm.V1.Func := seq.v1FuncAt []

def continuation (seq : Sequence H) (rest : List (HostSegment H)) : List Admin :=
  encode v1Syntax seq.root.tail rest

/-- The continuation expends the declared argument suffix, then checks the
following segments on the result types above the saved operands. -/
def checkRegion (fn : Function) (stack fallthrough : List NumType)
    (targets : List (List NumType)) : List (HostSegment H) → Bool
  | [] => fn.checkRegion stack fallthrough fn.code targets
  | segment :: rest =>
    checkHostPrefixWith (fn.declaration.params ++ fn.declaration.locals) stack segment.operands
      segment.site.signature (fun next => checkRegion fn next fallthrough targets rest)

def check (fn : Function) (stack : List NumType) (segments : List (HostSegment H)) : Bool :=
  checkRegion fn stack fn.declaration.results fn.entryLabels segments

def checkPath (seq : Sequence H) (stack fallthrough : List NumType) (targets : List (List NumType)) :
    List PathNode → Bool
  | [] => checkRegion seq.root.function stack fallthrough targets (seq.first :: seq.later)
  | node :: rest =>
    let fn := seq.root.function
    let result := node.block.result.toList
    let nested := result :: targets
    OpenLabel.checkTail fn (result.reverse ++ stack) fallthrough targets node.block.tail &&
    node.choice.all (fun test =>
      decide ((fn.declaration.params ++ fn.declaration.locals)[test.condition.toNat]? = some (.int .i32)) &&
        OpenLabel.checkTail fn [] result nested test.alternate) &&
    seq.checkPath [] result nested rest

structure Linked (site : HostCall.V1.Site H) (module : ModuleInst) (base : Store H) : Prop where
  resolved : module.funcs[site.index.toNat]? = some site.address
  allocated : base.funcs[site.address.value]? = some (.host site.signature site.target)
  scalar : site.signature.results.length ≤ 1

/-- Admission checks the actual full allocated body and every source site.
The final tail uses the original guarded Memory32 graph. -/
structure Checked (seq : Sequence H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (base : Store H) (outer : Frame) (args : List Value)
    (path : List PathNode := []) : Prop where
  resolved : outer.module.funcs[seq.root.index.toNat]? = some seq.root.address
  allocated : base.funcs[seq.root.address.value]? =
    some (.wasm seq.root.function.declaration.type seq.root.function.declaration.module (seq.v1FuncAt path))
  parameters : args.map Value.type = seq.root.function.declaration.params
  scalar : seq.root.function.declaration.results.length ≤ 1
  slot : seq.root.function.declaration.module.memories[0]? = some memory
  linkedHosts : ∀ site ∈ seq.sites, Linked site seq.root.function.declaration.module base
  typedBody : seq.checkPath (Prefix.stackTypes seq.root.function.initial) seq.root.function.declaration.results
    seq.root.function.entryLabels path = true
  guardedPath : PathNode.Allowed mode program memory calls seq.root.function path := by trivial
  supportedTail : supportedCode seq.root.function.code seq.root.function.entryLabels mode
    (program.checkIndirect calls seq.root.function.rank seq.root.function.declaration.module) = true
  linkedTail : ∀ target ∈ seq.root.function.targets,
    ∃ callee, program.lookup target.address = some callee ∧ callee.declaration = target.declaration ∧
      seq.root.function.declaration.module.funcs[target.index.toNat]? = some target.address ∧
      calls.permits seq.root.function.rank callee.rank

/-- The contract is applied at the current live store and actual typed inputs
of each reached site. All returned outcomes, including traps, are covered. -/
def Contract (seq : Sequence H) (host : HostSemantics H) (mode : MemoryMode) (memory : MemAddr)
    (initial : MemInst) (base : Store H) : Prop :=
  ∀ site ∈ seq.sites, ∀ bytes, mode.extent initial.data.size bytes →
    ∀ args : List Value, args.map Value.type = site.signature.params →
      site.ReturnContract host (HostStoreEffect mode memory initial) (storeWithBytes base memory initial bytes) args

inductive Phase (H : Type) where
  | call (path : List PathNode := [])
  | invoke (path : List PathNode := [])
  | path (stack : List Value) (node : PathNode) (rest : List PathNode) (labels : List OpenLabel)
  | test (stack : List Value) (block : PathBlock) (choice : PathChoice) (rest : List PathNode)
      (condition : BitVec 32) (labels : List OpenLabel)
  | computing (bytes : ByteArray) (stack : List Value) (remaining : List Prefix.Op)
      (site : HostCall.V1.Site H) (later : List (HostSegment H)) (labels : List OpenLabel := [])
  | pending (bytes : ByteArray) (saved args : List Value)
      (site : HostCall.V1.Site H) (later : List (HostSegment H)) (labels : List OpenLabel := [])
  | trapped (bytes : ByteArray) (saved : List Value) (tail : List Admin) (labels : List OpenLabel := [])
  | graph (state : State)

def beginPath (seq : Sequence H) (start : ByteArray) (stack : List Value) (labels : List OpenLabel) :
    List PathNode → Phase H
  | [] => .computing start stack seq.root.operands seq.root.site seq.later labels
  | node :: rest => .path stack node rest labels

def resume (seq : Sequence H) (outer : Frame) (args : List Value) (bytes : ByteArray)
    (stack : List Value) (later : List (HostSegment H)) (labels : List OpenLabel := []) : Phase H :=
  match later with
  | [] => .graph ⟨bytes, outer, (OpenLabel.context seq.root.function args labels).plug value (values stack ++ seq.root.tail)⟩
  | piece :: rest => .computing bytes stack piece.operands piece.site rest labels

def delivered (seq : Sequence H) (outer : Frame) (args : List Value) (bytes : ByteArray)
    (saved : List Value) (later : List (HostSegment H)) (r : Result) (labels : List OpenLabel := []) : Phase H :=
  match r with
  | .values payload => seq.resume outer args bytes (saved ++ payload) later labels
  | .trap => .trapped bytes saved (seq.continuation later) labels

def afterLabel (seq : Sequence H) (args : List Value) (labels : List OpenLabel)
    (code : List Admin) : List Admin :=
  [.frame seq.root.function.declaration.results.length (seq.root.function.declaration.frame args)
    ((OpenLabel.insert seq.root.function labels).plug value code)]

def render (seq : Sequence H) (base : Store H) (memory : MemAddr) (initial : MemInst)
    (start : ByteArray) (outer : Frame) (args : List Value) (phase : Phase H) : Config H :=
  let live bytes := storeWithBytes base memory initial bytes
  let k labels := OpenLabel.context seq.root.function args labels
  match phase with
  | .call _ => ⟨live start, outer, values args ++ [.source (.call seq.root.index)]⟩
  | .invoke _ => ⟨live start, outer, values args ++ [.invoke seq.root.address]⟩
  | .path stack node rest labels =>
    ⟨live start, outer, (k labels).plug value (values stack ++ expression (seq.sourcePath (node :: rest)))⟩
  | .test stack block choice rest condition labels =>
    ⟨live start, outer, (k labels).plug value (values (stack ++ [Value.int .i32 condition]) ++
      .source (.if_ block.result (seq.sourcePath rest) (v1Code choice.alternate)) :: expression (v1Code block.tail))⟩
  | .computing bytes stack ops site later labels =>
    ⟨live bytes, outer, (k labels).plug value (values stack ++ ops.map (Prefix.emit v1Syntax) ++
      .source (.call site.index) :: seq.continuation later)⟩
  | .pending bytes saved actual site later labels =>
    ⟨live bytes, outer, (k labels).plug value (values (saved ++ actual) ++ .invoke site.address :: seq.continuation later)⟩
  | .trapped bytes saved tail labels => ⟨live bytes, outer, (k labels).plug value (values saved ++ .trap :: tail)⟩
  | .graph state => Memory32.render base memory initial state

def ContextReady (seq : Sequence H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (labels : List OpenLabel) : Prop :=
  OpenLabel.Typed seq.root.function labels ∧ OpenLabel.Allowed mode program memory calls seq.root.function labels

def PathReady (seq : Sequence H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (labels : List OpenLabel) (stack : List Value) (path : List PathNode) : Prop :=
  seq.ContextReady mode program memory calls labels ∧
  PathNode.Allowed mode program memory calls seq.root.function path ∧
  seq.checkPath (Prefix.stackTypes stack) (OpenLabel.results seq.root.function labels)
    (OpenLabel.targets seq.root.function labels) path = true

/-- A pending site's invariant binds the actual arguments, the saved operands,
the remaining source checks, and the current shared extent. -/
def Ready (seq : Sequence H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (initial : MemInst) (phase : Phase H) (path : List PathNode := []) : Prop :=
  let fn := seq.root.function
  match phase with
  | .call current | .invoke current => current = path
  | .path stack node rest labels => seq.PathReady mode program memory calls labels stack (node :: rest)
  | .test stack block choice rest _ labels =>
    seq.PathReady mode program memory calls labels stack (⟨block, some choice⟩ :: rest)
  | .computing bytes stack ops site later labels =>
    mode.extent initial.data.size bytes ∧ site ∈ seq.sites ∧
      (∀ piece ∈ later, piece.site ∈ seq.sites) ∧
      checkHostPrefixWith (fn.declaration.params ++ fn.declaration.locals)
        (Prefix.stackTypes stack) ops site.signature
        (fun next => checkRegion fn next (OpenLabel.results fn labels) (OpenLabel.targets fn labels) later) = true ∧
      seq.ContextReady mode program memory calls labels
  | .pending bytes saved actual site later labels =>
    mode.extent initial.data.size bytes ∧ site ∈ seq.sites ∧
      (∀ piece ∈ later, piece.site ∈ seq.sites) ∧
      actual.map Value.type = site.signature.params ∧
      checkRegion fn (site.signature.results.reverse ++ Prefix.stackTypes saved)
        (OpenLabel.results fn labels) (OpenLabel.targets fn labels) later = true ∧
      seq.ContextReady mode program memory calls labels
  | .trapped bytes _ _ labels => mode.extent initial.data.size bytes ∧ seq.ContextReady mode program memory calls labels
  | .graph state => ReadyFor mode program memory calls (fn.rank + 1) initial.data.size state

/-- A step at one of the native entry, prefix, delivery or graph boundaries. -/
inductive Edge (seq : Sequence H) (host : HostSemantics H) (mode : MemoryMode)
    (program : Program) (memory : MemAddr) (base : Store H) (initial : MemInst)
    (start : ByteArray) (outer : Frame) (args : List Value) : Phase H → Phase H → Prop where
  | resolve {path} : Edge seq host mode program memory base initial start outer args (.call path) (.invoke path)
  | enter {path} : Edge seq host mode program memory base initial start outer args (.invoke path)
      (seq.beginPath start seq.root.function.initial [] path)
  | openBlock {stack block rest labels} :
      Edge seq host mode program memory base initial start outer args (.path stack ⟨block, none⟩ rest labels)
        (seq.beginPath start [] (⟨stack, block⟩ :: labels) rest)
  | readCondition {stack block choice rest condition labels}
      (found : (seq.root.function.declaration.frame args).locals[choice.condition.toNat]? =
        some (.int .i32 condition)) :
      Edge seq host mode program memory base initial start outer args
        (.path stack ⟨block, some choice⟩ rest labels) (.test stack block choice rest condition labels)
  | choosePath {stack block choice rest condition labels} (nonzero : condition ≠ 0) :
      Edge seq host mode program memory base initial start outer args
        (.test stack block choice rest condition labels) (.path stack ⟨block, none⟩ rest labels)
  | chooseAlternate {stack block choice rest labels} :
      Edge seq host mode program memory base initial start outer args (.test stack block choice rest 0 labels)
        (.graph ⟨start, outer, (OpenLabel.context seq.root.function args labels).plug value
          (values stack ++ .source (.block block.result (v1Code choice.alternate)) :: expression (v1Code block.tail))⟩)
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
        (.graph ⟨bytes, outer, seq.afterLabel args labels [.trap]⟩)
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
