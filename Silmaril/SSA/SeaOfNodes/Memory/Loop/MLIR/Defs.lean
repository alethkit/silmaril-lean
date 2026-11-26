module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Defs

/-! Lower an ordered, tail-tested memory loop to typed MLIR CF with a
fixed, initialized heap represented by scalar SSA values. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR

open RVSDG (Port Tuple)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg)
open Silmaril.MLIR.SCF.For (weakenVar)
open Memory.Diamond.MLIR (i64)
open Memory.Diamond.MLIR.Finite hiding entryTypes encodeEntry entryHeap lower Returns Label

variable {args : List ValueSort}

/-- The entry holds the initial heap and the invariant typed scalar input. -/
abbrev entryTypes (p : Profile) (args : List ValueSort) : List Width :=
  heapTypes p.cells ++ args.map (sortWidth p)

def encodeEntry (p : Profile) (input : Tuple (Val p.cells) args) (heap : Heap p.cells) :
    Env (entryTypes p args) :=
  (encodeHeap heap).append (encodeScalars p input)

inductive Label (p : Profile) : List Width → Type where
  | header : Label p (heapTypes p.cells)
  | test : Label p (resultTypes p)
  | exit : Label p (resultTypes p)

def entryVar (p : Profile) {sort : ValueSort} (port : Port args sort) :
    Var (entryTypes p args) (sortWidth p sort) :=
  weakenVar (argVar port) (heapTypes p.cells)

def entryHeap (p : Profile) (args : List ValueSort) : HeapRefs p.cells (entryTypes p args) :=
  fun index => appendVar (args.map (sortWidth p)) (cellVar index)

def headerRoute (p : Profile) (args : List ValueSort) :
    Routing p args [] (heapTypes p.cells ++ entryTypes p args)
  | _, .arg port => weakenVar (entryVar p port) (heapTypes p.cells)
  | _, .output index _ => index.elim0

def headerHeap (p : Profile) (args : List ValueSort) :
    HeapRefs p.cells (heapTypes p.cells ++ entryTypes p args) :=
  fun index => appendVar (entryTypes p args) (cellVar index)

/-- The body reads the arriving heap and passes its updated cells and word
to the tail test. -/
def headerBlock (p : Profile) (graph : Graph args) :
    Block Op (Label p) (heapTypes p.cells ++ entryTypes p args) (resultTypes p) :=
  lowerBody (fun word heap => .br ⟨.test, resultOperands word heap⟩) graph.body
    (headerRoute p args) (headerHeap p args)

def resultHeap (p : Profile) (args : List ValueSort) :
    HeapRefs p.cells (resultTypes p ++ entryTypes p args) :=
  fun index => appendVar (entryTypes p args) (.there (cellVar index))

/-- A matching word branches to exit. A mismatch supplies the next heap to
the header. The stop port is read from the dominating entry arguments. -/
def testBlock (p : Profile) (graph : Graph args) :
    Block Op (Label p) (resultTypes p ++ entryTypes p args) (resultTypes p) :=
  let stop := weakenVar (entryVar p graph.stop) (resultTypes p)
  let heap : HeapRefs p.cells _ := fun index => .there (resultHeap p args index)
  .letOp (.equal i64) (.cons .here (.cons stop .nil))
    (.terminator (.condBr .here
      ⟨.exit, resultOperands (.there .here) heap⟩
      ⟨.header, heapOperands heap⟩))

/-- Entry selects the initial heap; the test's backedge selects the last
store version. Both arrive at the same typed header argument list. -/
def lower (p : Profile) (graph : Graph args) : Cfg Op (Label p) (entryTypes p args) (resultTypes p) where
  entry := .terminator (.br ⟨.header, heapOperands (entryHeap p args)⟩)
  block
    | .header => headerBlock p graph
    | .test => testBlock p graph
    | .exit => .terminator (.ret (resultOperands .here (resultHeap p args)))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR
