module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Defs

/-! Delete one Store on both routes while retaining a disjoint entry Store. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (cell)
open Discovery.MemRef.CF (lowerDiamond)

variable {args : List ValueSort} {cells : Nat}

/-- Read the two original Stores in table order. The entry Return's word
is unused at the diamond boundary. -/
def stores : Memory.Graph args → Option (PrefixStore args × PrefixStore args)
  | .store _ (.arg x) (.arg a) (.store _ (.arg y) (.arg b) (.ret _ _)) =>
    some (⟨x, a⟩, ⟨y, b⟩)
  | _ => none

structure Edit (args : List ValueSort) where
  retained : PrefixStore args
  routes : Discovery.Result args

/-- The nominated version is one-based in the residual entry. Require
concretely distinct cells before discovering both route witnesses. -/
def rewrite (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) : Option (Edit args) := do
  let (first, second) ← stores entry
  if cell input first.address = cell input second.address then none else
    match version with
    | 1 => (Discovery.rewrite ⟨first, graph⟩ input).map (Edit.mk second)
    | 2 => (Discovery.rewrite ⟨second, graph⟩ input).map (Edit.mk first)
    | _ => none

/-- Run the entry-local pass, then try the nominated deletion on the
residual table. Refusal keeps the entry-local result. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) : Composition.Result cells args :=
  let repeated := Entry.lowerRepeated graph entry input
  match rewrite graph repeated.entry version input with
  | none => ⟨repeated.deleted, false, repeated.programs⟩
  | some edit => ⟨repeated.deleted, true, { repeated.programs with
      optimized := lowerDiamond cells edit.routes.graph (some edit.retained.table) }⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained
