module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Defs
public import Silmaril.SSA.RVSDG.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Theta.Defs

/-! # Numbered RVSDG θ over the ordered memory body -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open RVSDG (Origin Port Tuple Wires)
open RVSDG.OrderedRuntime.Structured
  (Instruction Opcode Threaded Ty newestIndex newestPort runtime runtimePort)
open RVSDG.NestedTheta (identityPorts thetaVertex)

abbrev carrier (args : List ValueSort) := Threaded (dataPorts args)
abbrev tested (args : List ValueSort) : List (Ty ValueSort) := .value .word :: dataPorts args
abbrev tagged (args : List ValueSort) : List (Ty ValueSort) := .control 2 :: dataPorts args

/-- The tail test sees the word from the body, then routes the invariant
arguments. Its ordered wrapper passes through the body's live heap. -/
inductive TailTest : RVSDG.Dialect ValueSort PUnit where
  | check {args : List ValueSort} (stop : Port args .word) : TailTest (tested args) (tagged args)

abbrev ThetaOpcode := Opcode TailTest Effect

def liftMemory {ins outs : List (Ty ValueSort)} (op : Opcode NoPure Effect ins outs) :
    ThetaOpcode ins outs :=
  match op with
  | .ordered _ _ (.pure op) => nomatch op
  | .ordered input output (.effect op) => .ordered input output (.effect op)

def continueTag (word stop : Word) : ULift (Fin 2) :=
  ⟨if word = stop then 0 else 1⟩

/-- Interpret the memory primitives with the existing ordered StateM model.
The extra pure tag vertex returns its input heap unchanged on its output wire. -/
def thetaRuntime (cells : Nat) : RVSDG.Model ThetaOpcode where
  value := Val cells
  state _ := Heap cells
  run op :=
    match op with
    | .ordered _ _ (.pure (.check stop)) => fun
      | .cons word payload => .cons (continueTag word (payload.get (argumentPort stop))) payload
    | .ordered ins outs (.effect op) =>
      (Memory.leafModel cells).toRVSDG.run (.ordered ins outs (.effect op))

variable {args : List ValueSort} {cells : Nat}

/-- Capture the original scalar arguments and take the heap from the supplied
live origin. The callback accounts for positions in the typed entry tuple. -/
def inputsWithHeap {entry : List (Ty ValueSort)} {past : List (List (Ty ValueSort))}
    (live : Origin entry past runtime) :
    (sorts : List ValueSort) →
    (∀ {t}, Port (carrier sorts) t → Origin entry past t) →
    Wires entry past (carrier sorts)
  | [], _ => .cons live .nil
  | _ :: rest, wire =>
    .cons (wire .head) (inputsWithHeap live rest (fun p => wire (.tail p)))

def newestWires {entry ports : List (Ty ValueSort)} (past : List (List (Ty ValueSort))) :
    Wires entry (past ++ [ports]) ports :=
  (identityPorts ports).map (fun _ p => .output (newestIndex ports past) (newestPort p past))

/-- Add the tag vertex at the acyclic body's return wires. Existing
operations and their order are retained. -/
def testAfter (stop : Port args .word) :
    {past sigs : List (List (Ty ValueSort))} →
    RVSDG.Term ThetaOpcode (carrier args) past sigs (Threaded wordPorts) →
    RVSDG.Term ThetaOpcode (carrier args) past (sigs ++ [Threaded (tagged args)]) (Threaded (tagged args))
  | past, _, .ret wires =>
    let word := wires.get .head
    let live := wires.get (.tail .head)
    let op : Instruction TailTest Effect (tested args) (tagged args) := .pure (.check stop)
    let node : RVSDG.Node ThetaOpcode (carrier args) past (Threaded (tagged args)) :=
      ⟨Threaded (tested args), .simple (.ordered (.value (inputData args)) (.control (inputData args)) op),
        .cons word (inputsWithHeap live args (fun p => .arg p)), fun i => i.elim0⟩
    .bind node (fun i => i.elim0) (.ret (newestWires past))
  | _, _, .bind node children rest => .bind node children (testAfter stop rest)

abbrev Graph.thetaSigs (graph : Graph args) :=
  graph.body.targetSigs ++ [Threaded (tagged args)]

def Graph.thetaBody (graph : Graph args) :
    RVSDG.Term ThetaOpcode (carrier args) [] graph.thetaSigs (RVSDG.Theta.BodyResults (carrier args)) :=
  testAfter graph.stop (RVSDG.Institution.mapTerm liftMemory graph.body.lowered.term)

/-- Stop and continue both return the post-effect heap. On exit the tested
word equals the invariant stop word, so the latter is the scalar result wire. -/
def Graph.lowerThetaTerm (graph : Graph args) :
    RVSDG.NestedTheta.Term ThetaOpcode (carrier args) [] [carrier args] (Threaded wordPorts) :=
  .bind (thetaVertex graph.thetaSigs) (fun _ => .ofBase graph.thetaBody)
    (.ret (.cons (.output (0 : Fin 1) (argumentPort graph.stop))
      (.cons (.output (0 : Fin 1) (runtimePort (dataPorts args))) .nil)))

def Graph.lowerTheta (graph : Graph args) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier args) [] [carrier args] (Threaded wordPorts) :=
  graph.lowerThetaTerm.toGraph

end Silmaril.SSA.SeaOfNodes.Memory.Loop
