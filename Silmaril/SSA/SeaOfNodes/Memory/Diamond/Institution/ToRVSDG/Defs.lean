module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Defs
public import Silmaril.SSA.RVSDG.Institution.Defs

/-! Native memory diamond equations observed at the actual numbered RVSDG
boundary, using each program's Region order to encode the Boolean guard. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Opcode Threaded Ty)
open SeaOfNodes.Diamond (Merge)

variable {P : Signature} {args : List ValueSort}

/-- The ordinary numbered RVSDG signature of the memory lowering. -/
abbrev targetSignature : RVSDG.Institution.Signature ValueSort PUnit :=
  ⟨Opcode NoPure Effect⟩

/-- A numbered graph at the diamond boundary together with the order
used to encode its input selector. -/
structure Program (args : List ValueSort) where
  merge : Merge
  sigs : List (List (Ty ValueSort))
  graph : RVSDG.Graph targetSignature.op (Threaded (inputPorts args)) [] sigs (Threaded wordPorts)

/-- Keep the original numbering, predecessor order and suffix. -/
def Program.ofGraph (graph : Graph args) : Program args :=
  ⟨graph.merge, _, graph.lower⟩

/-- Execute the numbered graph on the scalar valuation and initial heap.
Both the returned word and the final heap are in the result tuple. -/
def Program.observe (program : Program P.args) (model : Model P) (guard : Bool)
    (initial : Heap model.cells) : Tuple (WireVal model.cells) (Threaded wordPorts) :=
  program.graph.run (leafModel model.cells).toRVSDG
    (encodeEntry program.merge guard model.input initial)

structure CompiledEquation (P : Signature) where
  lhs : Program P.args
  rhs : Program P.args

def translateEquation (e : Equation P) : CompiledEquation P :=
  ⟨Program.ofGraph e.lhs, Program.ofGraph e.rhs⟩

/-- At this valuation, quantify over the shared Boolean guard and heap.
Each side encodes the guard at its own numbered predecessor position. -/
def CompiledEquation.Holds (e : CompiledEquation P) (model : Model P) : Prop :=
  ∀ guard initial, e.lhs.observe model guard initial = e.rhs.observe model guard initial

/-- A room at this typed entry, with the fixed memory interpretation. -/
def room (P : Signature) : Room.{0, 0, 0} where
  Sen := CompiledEquation P
  Mod := Cat.of (Discrete (Model P))
  Sat model e := e.Holds model.as

/-- Compare the same numbered graphs in the existing RVSDG room, which
feeds a single raw input tuple to both sides. -/
def CompiledEquation.sharedInputEquation (e : CompiledEquation P) :
    RVSDG.Institution.Equation targetSignature.op :=
  ⟨Threaded (inputPorts P.args), Threaded wordPorts, e.lhs.sigs, e.rhs.sigs, e.lhs.graph, e.rhs.graph⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG
