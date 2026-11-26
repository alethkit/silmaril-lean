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

open Execution.Runtime (Frame MemAddr MemInst ModuleInst Result Value)
open Computed
open Wasm.V1.Execution

structure HostSegment (H : Type) where
  operands : List Prefix.Op
  site : HostCall.V1.Site H

/-- The root describes the first site and the shared final graph tail. -/
structure Sequence (H : Type) where
  root : HostEntry H
  later : List (HostSegment H)

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

def v1Func (seq : Sequence H) : Wasm.V1.Func :=
  let fn := seq.root.function
  ⟨fn.declaration.typeIndex, fn.declaration.locals,
    fn.initial.map Graph.v1CodeSyntax.ops.value ++
      encode Graph.v1CodeSyntax.ops (v1Code fn.code) (seq.first :: seq.later)⟩

def continuation (seq : Sequence H) (rest : List (HostSegment H)) : List Admin :=
  encode v1Syntax seq.root.tail rest

/-- The continuation checker consumes ordered host parameters, adds the
declared results and checks the next segment above the preserved prefix. -/
def check (fn : Function) (stack : List NumType) : List (HostSegment H) → Bool
  | [] => fn.checkCode stack fn.code
  | segment :: rest =>
    checkHostPrefixWith (fn.declaration.params ++ fn.declaration.locals) stack segment.operands
      segment.site.signature (fun next => check fn next rest)

structure Linked (site : HostCall.V1.Site H) (module : ModuleInst) (base : Store H) : Prop where
  resolved : module.funcs[site.index.toNat]? = some site.address
  allocated : base.funcs[site.address.value]? = some (.host site.signature site.target)
  scalar : site.signature.results.length ≤ 1

/-- Admission checks the actual full allocated body and every source site.
The final tail uses the original guarded Memory32 graph. -/
structure Checked (seq : Sequence H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (base : Store H) (outer : Frame) (args : List Value) : Prop where
  resolved : outer.module.funcs[seq.root.index.toNat]? = some seq.root.address
  allocated : base.funcs[seq.root.address.value]? =
    some (.wasm seq.root.function.declaration.type seq.root.function.declaration.module seq.v1Func)
  parameters : args.map Value.type = seq.root.function.declaration.params
  scalar : seq.root.function.declaration.results.length ≤ 1
  slot : seq.root.function.declaration.module.memories[0]? = some memory
  linkedHosts : ∀ site ∈ seq.sites, Linked site seq.root.function.declaration.module base
  typedBody : check seq.root.function (Prefix.stackTypes seq.root.function.initial) (seq.first :: seq.later) = true
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
  | call
  | invoke
  | computing (bytes : ByteArray) (stack : List Value) (remaining : List Prefix.Op)
      (site : HostCall.V1.Site H) (later : List (HostSegment H))
  | pending (bytes : ByteArray) (saved args : List Value)
      (site : HostCall.V1.Site H) (later : List (HostSegment H))
  | trapped (bytes : ByteArray) (saved : List Value) (tail : List Admin)
  | graph (state : State)

def resume (seq : Sequence H) (outer : Frame) (args : List Value) (bytes : ByteArray)
    (stack : List Value) : List (HostSegment H) → Phase H
  | [] => .graph ⟨bytes, outer, (seq.root.context args).plug value (values stack ++ seq.root.tail)⟩
  | piece :: later => .computing bytes stack piece.operands piece.site later

def delivered (seq : Sequence H) (outer : Frame) (args : List Value) (bytes : ByteArray)
    (saved : List Value) (later : List (HostSegment H)) : Result → Phase H
  | .values payload => seq.resume outer args bytes (saved ++ payload) later
  | .trap => .trapped bytes saved (seq.continuation later)

def render (seq : Sequence H) (base : Store H) (memory : MemAddr) (initial : MemInst)
    (start : ByteArray) (outer : Frame) (args : List Value) (phase : Phase H) : Config H :=
  let live bytes := storeWithBytes base memory initial bytes
  let k := seq.root.context args
  match phase with
  | .call => ⟨live start, outer, values args ++ [.source (.call seq.root.index)]⟩
  | .invoke => ⟨live start, outer, values args ++ [.invoke seq.root.address]⟩
  | .computing bytes stack ops site later =>
    ⟨live bytes, outer, k.plug value (values stack ++ ops.map (Prefix.emit v1Syntax) ++
      .source (.call site.index) :: seq.continuation later)⟩
  | .pending bytes saved actual site later =>
    ⟨live bytes, outer, k.plug value (values (saved ++ actual) ++ .invoke site.address :: seq.continuation later)⟩
  | .trapped bytes saved tail => ⟨live bytes, outer, k.plug value (values saved ++ .trap :: tail)⟩
  | .graph state => Memory32.render base memory initial state

/-- A pending site's invariant binds the actual arguments, the saved operands,
the remaining source checks, and the current shared extent. -/
def Ready (seq : Sequence H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (initial : MemInst) : Phase H → Prop
  | .call | .invoke => True
  | .computing bytes stack ops site later =>
    mode.extent initial.data.size bytes ∧ site ∈ seq.sites ∧
      (∀ piece ∈ later, piece.site ∈ seq.sites) ∧
      checkHostPrefixWith (seq.root.function.declaration.params ++ seq.root.function.declaration.locals)
        (Prefix.stackTypes stack) ops site.signature (fun next => check seq.root.function next later) = true
  | .pending bytes saved actual site later =>
    mode.extent initial.data.size bytes ∧ site ∈ seq.sites ∧
      (∀ piece ∈ later, piece.site ∈ seq.sites) ∧
      actual.map Value.type = site.signature.params ∧
      check seq.root.function (site.signature.results.reverse ++ Prefix.stackTypes saved) later = true
  | .trapped bytes .. => mode.extent initial.data.size bytes
  | .graph state => ReadyFor mode program memory calls (seq.root.function.rank + 1) initial.data.size state

/-- A step at one of the native entry, prefix, delivery or graph boundaries. -/
inductive Edge (seq : Sequence H) (host : HostSemantics H) (mode : MemoryMode)
    (program : Program) (memory : MemAddr) (base : Store H) (initial : MemInst)
    (start : ByteArray) (outer : Frame) (args : List Value) : Phase H → Phase H → Prop where
  | resolve : Edge seq host mode program memory base initial start outer args .call .invoke
  | enter : Edge seq host mode program memory base initial start outer args .invoke
      (.computing start seq.root.function.initial seq.root.operands seq.root.site seq.later)
  | numeric {bytes stack next op rest site later}
      (move : Prefix.Reduce (seq.root.function.declaration.frame args).locals stack op (.values next)) :
      Edge seq host mode program memory base initial start outer args (.computing bytes stack (op :: rest) site later)
        (.computing bytes next rest site later)
  | prefixTrap {bytes stack saved op rest site later}
      (move : Prefix.Reduce (seq.root.function.declaration.frame args).locals stack op (.trap saved)) :
      Edge seq host mode program memory base initial start outer args (.computing bytes stack (op :: rest) site later)
        (.trapped bytes saved (rest.map (Prefix.emit v1Syntax) ++ .source (.call site.index) :: seq.continuation later))
  | discard {bytes saved tail kept rest} (move : Prefix.Discard saved tail kept rest) :
      Edge seq host mode program memory base initial start outer args (.trapped bytes saved tail) (.trapped bytes kept rest)
  | closeTrap {bytes} :
      Edge seq host mode program memory base initial start outer args (.trapped bytes [] [])
        (.graph ⟨bytes, outer, [.frame seq.root.function.declaration.results.length
          (seq.root.function.declaration.frame args) [.trap]]⟩)
  | hostResolve {bytes saved actual site later} (typed : actual.map Value.type = site.signature.params) :
      Edge seq host mode program memory base initial start outer args (.computing bytes (saved ++ actual) [] site later)
        (.pending bytes saved actual site later)
  | returned {bytes saved actual site later after r next}
      (behavior : host site.target (storeWithBytes base memory initial bytes) actual (.returned after r))
      (stored : after = storeWithBytes base memory initial next) :
      Edge seq host mode program memory base initial start outer args (.pending bytes saved actual site later)
        (seq.delivered outer args next saved later r)
  | diverged {bytes saved actual site later}
      (behavior : host site.target (storeWithBytes base memory initial bytes) actual .diverged) :
      Edge seq host mode program memory base initial start outer args (.pending bytes saved actual site later)
        (.pending bytes saved actual site later)
  | graph {src dst} (move : EdgeAt mode program memory src dst) :
      Edge seq host mode program memory base initial start outer args (.graph src) (.graph dst)

abbrev Runs (seq : Sequence H) (host : HostSemantics H) (mode : MemoryMode)
    (program : Program) (memory : MemAddr) (base : Store H) (initial : MemInst)
    (start : ByteArray) (outer : Frame) (args : List Value) :=
  Relation.ReflTransGen (seq.Edge host mode program memory base initial start outer args)

end Sequence
end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry
