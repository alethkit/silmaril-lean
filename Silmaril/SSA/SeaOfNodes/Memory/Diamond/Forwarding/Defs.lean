module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Defs

/-! # Checked forwarding of a post-join Load -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding

open RVSDG (Port)

variable {args : List ValueSort}

/-- The two proposed last Store versions, in Region input order. -/
structure Candidate where
  firstStore : Nat
  secondStore : Nat

/-- Check both incoming occurrences against the shared Load address. Each
arm must export its own matching Store word alongside its final memory. -/
def checkJoined (graph : Graph args) (address : Port args .address) (candidate : Candidate) : Bool :=
  Memory.Forwarding.checkExit (graph.arm (graph.merge.predecessor .first)) address candidate.firstStore &&
  Memory.Forwarding.checkExit (graph.arm (graph.merge.predecessor .second)) address candidate.secondStore

/-- This profile rewrites the first operation after the join when it is a
Load from an original argument address. The suffix may use that Load
in any later word operands, including later Stores. -/
def rewriteSuffixUsing (check : Port args .address → Bool) :
    Memory.Graph (.word :: args) → Option (Memory.Graph (.word :: args))
  | .load _ (.arg (.tail address)) rest =>
    if check address then
      some (Memory.Forwarding.rewire rest (Memory.Forwarding.dropLoad (.arg .head)))
    else none
  | _ => none

def rewriteSuffix (graph : Graph args) (candidate : Candidate) :
    Memory.Graph (.word :: args) → Option (Memory.Graph (.word :: args)) :=
  rewriteSuffixUsing (fun address => checkJoined graph address candidate)

/-- Use an address check to redirect the initial suffix Load's word users. -/
def rewriteUsing (graph : Graph args) (check : Port args .address → Bool) : Option (Graph args) :=
  (rewriteSuffixUsing check graph.suffix).map (fun suffix => { graph with suffix })

/-- Replace the shared Load by a wire to the scalar already latched at the
same occurrence as the heap. -/
def rewrite (graph : Graph args) (candidate : Candidate) : Option (Graph args) :=
  rewriteUsing graph (fun address => checkJoined graph address candidate)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding
