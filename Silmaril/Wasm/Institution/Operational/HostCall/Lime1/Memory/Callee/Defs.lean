module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee

open Execution.Runtime (Frame Result Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall.Ranked

/-- After entry the arguments determine the same frame until it is popped.
The relation carries live bytes separately from the frame and its operands. -/
inductive Phase (H : Type) where
  | invoke (args : List Value)
  | body (args stack : List Value) (ops : List Graph.Memory32.Op)
  | child (args saved : List Value) (callee : MemoryTarget) (phase : Phase H) (rest : List Graph.Memory32.Op)
  | hostInvoke (args saved : List Value) (target : Site H) (operands : List Value) (rest : List Graph.Memory32.Op)
  | trapped (args stack : List Value) (rest : List Admin)
  | exit (args : List Value) (out : Result)
  | done (out : Result)

def code (ops : List Graph.Memory32.Op) : List Admin :=
  expression (ops.map fun op => op.v1.toLime)

def resultTyped (callee : MemoryTarget) : Result → Prop
  | .values vs => vs.map Value.type = callee.fn.declaration.results
  | .trap => True

/-- Live bodies and suspended suffixes come from their registered function.
This lets a reached lookup use the link checked for its source instruction. -/
def Ready {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H) (site : IndirectSite)
    (callee : MemoryTarget) : Phase H → Prop
  | .invoke args | .trapped args _ _ => args.map Value.type = callee.fn.declaration.params
  | .body args stack ops => args.map Value.type = callee.fn.declaration.params ∧
      ops.all (MemoryTarget.supportedOp mem.extent.growthEnabled) = true ∧ callee.fn.WellTyped stack ops ∧
      ∀ op ∈ ops, op ∈ callee.fn.code
  | .child args saved child phase rest =>
      args.map Value.type = callee.fn.declaration.params ∧
      site.memoryLookup child.address = some child.fn ∧ child.Allocated base ∧ child.fn.rank < callee.fn.rank ∧
      (∀ out, phase ≠ .done out) ∧ Ready mem host site child phase ∧
      rest.all (MemoryTarget.supportedOp mem.extent.growthEnabled) = true ∧
      (∀ op ∈ rest, op ∈ callee.fn.code) ∧
      ∀ vs : List Value, vs.map Value.type = child.fn.declaration.results → callee.fn.WellTyped (saved ++ vs) rest
  | .hostInvoke args saved target operands rest =>
      args.map Value.type = callee.fn.declaration.params ∧
      target.Allocated base ∧ target.Arguments operands ∧ target.Contract mem host ∧
      rest.all (MemoryTarget.supportedOp mem.extent.growthEnabled) = true ∧
      (∀ op ∈ rest, op ∈ callee.fn.code) ∧
      ∀ vs : List Value, target.TypedResult (.values vs) → callee.fn.WellTyped (saved ++ vs) rest
  | .exit args out => args.map Value.type = callee.fn.declaration.params ∧ resultTyped callee out
  | .done out => resultTyped callee out

def render {H : Type} (callee : MemoryTarget) : Phase H → List Admin
  | .invoke args => values args ++ [.invoke callee.address]
  | .body args stack ops => [.frame callee.fn.declaration.results.length (callee.fn.declaration.frame args)
      [.label callee.fn.declaration.results.length [] (values stack ++ code ops)]]
  | .child args saved child phase rest =>
      [.frame callee.fn.declaration.results.length (callee.fn.declaration.frame args)
        [.label callee.fn.declaration.results.length [] (values saved ++ render child phase ++ code rest)]]
  | .hostInvoke args saved target operands rest =>
      [.frame callee.fn.declaration.results.length (callee.fn.declaration.frame args)
        [.label callee.fn.declaration.results.length []
          (values (saved ++ operands) ++ .invoke target.address :: code rest)]]
  | .trapped args stack rest => [.frame callee.fn.declaration.results.length (callee.fn.declaration.frame args)
      [.label callee.fn.declaration.results.length [] (values stack ++ .trap :: rest)]]
  | .exit args out => [.frame callee.fn.declaration.results.length (callee.fn.declaration.frame args) (result out)]
  | .done out => result out

def afterChild {H : Type} (args saved : List Value) (child : MemoryTarget) (rest : List Graph.Memory32.Op) : Phase H → Phase H
  | .done (.values vs) => .body args (saved ++ vs) rest
  | .done .trap => .trapped args saved (code rest)
  | phase => .child args saved child phase rest

def config {H : Type} {base : Store H} (mem : Memory32 base) (caller : Frame)
    (saved : List Value) (tail : List Admin) (callee : MemoryTarget) (bytes : ByteArray)
    (phase : Phase H) : Config H :=
  ⟨mem.store bytes, caller, values saved ++ render callee phase ++ tail⟩

/-- The page count encoded as the i32 result of a size or successful grow. -/
def pages (bytes : ByteArray) : Value :=
  .int .i32 (BitVec.ofNat 32 (Execution.Memory.size bytes))

inductive Edge {H : Type} {base : Store H} (mem : Memory32 base)
    (host : HostSemantics H) (site : IndirectSite) : MemoryTarget → ByteArray → Phase H → ByteArray → Phase H → Prop where
  | enter {callee bytes args} : Edge mem host site callee bytes (.invoke args) bytes (.body args callee.fn.initial callee.fn.code)
  | get {callee bytes args stack index ops v}
      (found : (callee.fn.declaration.frame args).locals[index.toNat]? = some v) :
      Edge mem host site callee bytes (.body args stack (.ranked (.numeric (.get index)) :: ops))
        bytes (.body args (stack ++ [v]) ops)
  | load {callee bytes args saved offset ptr ops bits}
      (read : MemoryQuery.EdgeAt bytes offset.val (.load ptr) (.value bits)) :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 ptr]) (.load offset :: ops))
        bytes (.body args (saved ++ [Value.int .i32 bits]) ops)
  | loadTrap {callee bytes args saved offset ptr ops}
      (read : MemoryQuery.EdgeAt bytes offset.val (.load ptr) .trap) :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 ptr]) (.load offset :: ops))
        bytes (.trapped args saved (code ops))
  | store {callee bytes written args saved offset ptr word ops}
      (write : MemoryWrite.EdgeAt bytes offset.val (.store ptr word) (.written written)) :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 ptr, Value.int .i32 word]) (.store offset :: ops))
        written (.body args saved ops)
  | storeTrap {callee bytes args saved offset ptr word ops}
      (write : MemoryWrite.EdgeAt bytes offset.val (.store ptr word) .trap) :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 ptr, Value.int .i32 word]) (.store offset :: ops))
        bytes (.trapped args saved (code ops))
  | size {callee bytes args stack ops} :
      Edge mem host site callee bytes (.body args stack (.size :: ops)) bytes (.body args (stack ++ [pages bytes]) ops)
  | grow {callee bytes grown args saved delta ops} (enabled : mem.extent.growthEnabled = true)
      (move : MemoryGrow.Edge (mem.current bytes) (.request delta) (.grown grown)) :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 delta]) (.grow :: ops))
        grown (.body args (saved ++ [pages bytes]) ops)
  | growFail {callee bytes args saved delta ops} :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 delta]) (.grow :: ops))
        bytes (.body args (saved ++ [Value.int .i32 (-1)]) ops)
  | call {callee child bytes args saved operands target rest}
      (link : site.MemoryDirect (base := base) callee target child)
      (typed : operands.map Value.type = target.declaration.params) :
      Edge mem host site callee bytes (.body args (saved ++ operands) (.ranked (.call target) :: rest))
        bytes (.child args saved child (.invoke operands) rest)
  | callIndirect {callee child bytes args saved operands index signature selector rest}
      (lookup : (site.memorySite index signature).Lookup base selector (some (.memory child)))
      (smaller : child.fn.rank < callee.fn.rank)
      (typed : operands.map Value.type = signature.params) :
      Edge mem host site callee bytes (.body args ((saved ++ operands) ++ [Value.int .i32 selector])
        (.callIndirect index signature :: rest)) bytes (.child args saved child (.invoke operands) rest)
  | callIndirectHost {callee target bytes args saved operands index signature selector rest}
      (lookup : (site.memorySite index signature).Lookup base selector (some (.host target)))
      (typed : operands.map Value.type = signature.params) :
      Edge mem host site callee bytes (.body args ((saved ++ operands) ++ [Value.int .i32 selector])
        (.callIndirect index signature :: rest)) bytes (.hostInvoke args saved target operands rest)
  | indirectTrap {callee bytes args stack index signature selector rest}
      (lookup : (site.memorySite index signature).Lookup base selector none) :
      Edge mem host site callee bytes (.body args (stack ++ [Value.int .i32 selector])
        (.callIndirect index signature :: rest)) bytes (.trapped args stack (code rest))
  | hostReturned {callee target bytes written args saved operands rest vs} (live : mem.Live written)
      (typed : target.TypedResult (.values vs))
      (answer : host target.code (mem.store bytes) operands (.returned (mem.store written) (.values vs))) :
      Edge mem host site callee bytes (.hostInvoke args saved target operands rest)
        written (.body args (saved ++ vs) rest)
  | hostTrapped {callee target bytes written args saved operands rest} (live : mem.Live written)
      (answer : host target.code (mem.store bytes) operands (.returned (mem.store written) .trap)) :
      Edge mem host site callee bytes (.hostInvoke args saved target operands rest)
        written (.trapped args saved (code rest))
  | hostDiverged {callee target bytes args saved operands rest}
      (answer : host target.code (mem.store bytes) operands .diverged) :
      Edge mem host site callee bytes (.hostInvoke args saved target operands rest)
        bytes (.hostInvoke args saved target operands rest)
  | child {callee child bytes written args saved phase next rest}
      (move : Edge mem host site child bytes phase written next) :
      Edge mem host site callee bytes (.child args saved child phase rest)
        written (afterChild args saved child rest next)
  | erase {callee bytes args stack kept removed before cut rest}
      (split : stack = kept ++ removed) (suffix : before = cut ++ rest) (active : removed ≠ [] ∨ cut ≠ []) :
      Edge mem host site callee bytes (.trapped args stack before) bytes (.trapped args kept rest)
  | labelDone {callee bytes args vs} : Edge mem host site callee bytes (.body args vs []) bytes (.exit args (.values vs))
  | labelTrap {callee bytes args} : Edge mem host site callee bytes (.trapped args [] []) bytes (.exit args .trap)
  | frameDone {callee bytes args out} : Edge mem host site callee bytes (.exit args out) bytes (.done out)

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee
