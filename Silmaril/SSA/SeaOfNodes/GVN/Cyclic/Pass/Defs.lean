module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Defs

/-!
# Discover one shrinking cyclic GVN step

Enumerate producer deletions and typed header redirects. A redirect is
returned only as part of an accepted deletion on its edited header.
The caller supplies the certified cyclic view of the current loop.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass

open Diamond (Dataflow Signature Ty ValueSort dataPorts)
open RVSDG (Origin Port)
open Activation (View sourceWire)
open Deletion (DeletedLoop)
open Elimination (inFinal operandScope)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)}

/-- Enumerate every typed producer reference in table order. -/
def producers :
    {past sigs : List (List (Ty Data))} → (flow : Dataflow Op args past sigs) →
      List (Σ sort, Producer flow sort)
  | _, _, .nil => []
  | _, _, .cons (out := out) _ _ rest =>
    ⟨out, .here⟩ :: (producers rest).map (fun ⟨sort, ref⟩ => ⟨sort, .later ref⟩)

/-- Enumerate the ordered operand occurrences of a typed signature. -/
def operandPorts : (ins : List (ValueSort Data)) →
    List (Σ sort, Port (dataPorts ins) (.value sort))
  | [] => []
  | sort :: rest => ⟨sort, .head⟩ :: (operandPorts rest).map (fun ⟨s, port⟩ => ⟨s, .tail port⟩)

abbrev OutputWire (args : List (Ty Data)) (scope : List (List (Ty Data))) :=
  Σ sort, Origin args scope (.value sort)

/-- Extend the available output list as each binding before the consumer
comes into scope. At a loop header the initial producer scope is empty. -/
def prefixOutputs :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → (consumer : Producer flow out) →
      List (OutputWire args past) → List (OutputWire args (operandScope consumer))
  | _, _, _, _, .here, available => available
  | _, _, _, _, .later (out := head) consumer, available =>
    let earlier := available.map (fun ⟨sort, wire⟩ => ⟨sort, weaken [.value head] wire⟩)
    prefixOutputs consumer (earlier ++ [⟨head, newest .head⟩])

variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {n : Nat} {sorts : Fin n → ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {g : Cyclic.Graph Op inputs sorts}

structure Redirect (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (sorts : Fin n → ValueSort Data) where
  consumerOut : ValueSort Data
  consumer : Producer loop.header consumerOut
  sort : ValueSort Data
  use : Port (dataPorts consumer.key.ins) (.value sort)
  original : Source inputs sorts sort
  representative : Source inputs sorts sort
  wire : Origin (Loop.headerPorts inputs carried) (operandScope consumer) (.value sort)

inductive Proposal (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (sorts : Fin n → ValueSort Data) where
  | delete {sort : ValueSort Data} (candidate : Producer loop.header sort)
  | redirect (edit : Redirect loop sorts)

/-- Scan the current header in order for an unused producer. -/
def firstDeletion? (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    Option (DeletedLoop Op inputs carried entrySigs out) :=
  (producers loop.header).findSome? (fun ⟨_, candidate⟩ => Deletion.delete? loop candidate)

variable [DecidableEq (ValueSort Data)]

/-- Pair the selected old operand with available header outputs.
The view supplies all same-sort source names for those actual addresses. -/
def redirects (view : View g loop) (selected : Σ sort, Producer loop.header sort) :
    List (Redirect loop sorts) :=
  let ⟨consumerOut, consumer⟩ := selected
  let available := prefixOutputs consumer []
  (operandPorts consumer.key.ins).flatMap fun ⟨sort, use⟩ =>
    let sources := (List.finRange n).filterMap fun i =>
      if same : sorts i = sort then some (Source.producer (inputs := inputs) i same) else none
    let oldAddress := (inFinal consumer (HeaderUse.operandAt consumer use)).address
    let originals := sources.filter (fun source => (sourceWire view.site source).address == oldAddress)
    originals.flatMap fun original =>
      available.flatMap fun ⟨wireSort, wire⟩ =>
        if same : wireSort = sort then
          let prefixWire : Origin (Loop.headerPorts inputs carried) (operandScope consumer) (.value sort) :=
            same ▸ wire
          let address := (inFinal consumer prefixWire).address
          (sources.filter (fun source => (sourceWire view.site source).address == address)).map
            (fun representative => ⟨consumerOut, consumer, sort, use, original, representative, prefixWire⟩)
        else []

/-- Try direct deletions first, then redirections in header and operand order. -/
def proposals (view : View g loop) : List (Proposal loop sorts) :=
  let all := producers loop.header
  (all.map fun ⟨_, candidate⟩ => .delete candidate) ++
    (all.flatMap fun selected => (redirects view selected).map Proposal.redirect)

variable [∀ ins out, DecidableEq (Op ins out)]

/-- Run the existing checks on a typed proposal. A redirect without a
successful deletion produces no result. -/
def tryProposal? (view : View g loop) (p : Partition n) :
    Proposal loop sorts → Option (DeletedLoop Op inputs carried entrySigs out)
  | .delete candidate => Deletion.delete? loop candidate
  | .redirect edit =>
    (HeaderUse.redirect? view p edit.consumer edit.use edit.original edit.representative edit.wire).bind
      firstDeletion?

/-- Discover the first accepted shrinking step using the stable partition
computed from the supplied view's graph. -/
def step? (view : View g loop) : Option (DeletedLoop Op inputs carried entrySigs out) :=
  let p := FixedPoint.normalize g
  (proposals view).findSome? (tryProposal? view p)

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass
