module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Defs

/-! Partial initialization and invocation of one typed ω export. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation

open Continuation.Partial
open Continuation.Partial.CallDescent (Entry)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}

/-- A single unit's supplied imports, selected callable export, and invocation arguments. -/
structure Request (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) (results : Ports (Ty V S)) where
  unitId : Nat
  imports : Ports (Ty V S)
  exports : Ports (Ty V S)
  sigs : List (Ports (Ty V S))
  graph : Omega Op imports exports sigs
  imported : Tuple m.Val imports
  params : Ports (Ty V S)
  port : Port exports (.value (.function params results))
  arguments : Tuple m.Val params
  initialStore : σ

variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {results : Ports (Ty V S)}

def Request.Links (request : Request m σ results) (primitives : Primitives m σ)
    (outcome : PartialLink.Outcome m σ request.exports) : Prop :=
  PartialLink.Links primitives request.unitId request.graph request.imported request.initialStore outcome

/-- Prepare a typed call of the published callable with the post-link store. -/
def Request.entry (request : Request m σ results) (exports : Tuple m.Val request.exports)
    (store : σ) : Entry m σ :=
  ⟨⟨results, ⟨request.params, exports.get request.port, request.arguments⟩⟩, store⟩

/-- Dispatch the actual partial link result to the existing continuation
machine. An initializer failure is reported before creating an invocation. -/
noncomputable def Request.start (request : Request m σ results) (primitives : Primitives m σ) :
    Except (Failure m σ) (Config m σ results) :=
  match PartialLink.link primitives request.unitId request.graph request.imported request.initialStore with
  | .undefined failure => .error failure
  | .linked exports store => .ok ((request.entry exports store).config .halt)

/-- An invocation outcome can only follow a successful partial link. -/
def Request.AfterLink (request : Request m σ results) (primitives : Primitives m σ)
    (outcome : Tuple m.Val request.exports → σ → Prop) : Prop :=
  ∃ exports store, request.Links primitives (.linked exports store) ∧ outcome exports store

def Request.LinkBlocks (request : Request m σ results) (primitives : Primitives m σ) : Prop :=
  ∃ failure, request.Links primitives (.undefined failure)

def Request.Returns (request : Request m σ results) (primitives : Primitives m σ) : Prop :=
  request.AfterLink primitives fun exports store => Classification.Returns primitives (request.entry exports store)

def Request.Blocks (request : Request m σ results) (primitives : Primitives m σ) : Prop :=
  request.AfterLink primitives fun exports store => Classification.Blocks primitives (request.entry exports store)

def Request.Diverges (request : Request m σ results) (primitives : Primitives m σ) : Prop :=
  request.AfterLink primitives fun exports store => Divergence.Diverges primitives (request.entry exports store)

/-- Exhaustiveness and pairwise exclusivity for initialization followed
by the selected invocation under the same partial interpretation. -/
structure Outcomes (request : Request m σ results) (primitives : Primitives m σ) : Prop where
  exhaustive : request.LinkBlocks primitives ∨ request.Returns primitives ∨
    request.Blocks primitives ∨ request.Diverges primitives
  link_block_exclusive : request.LinkBlocks primitives →
    ¬ request.Returns primitives ∧ ¬ request.Blocks primitives ∧ ¬ request.Diverges primitives
  return_exclusive : request.Returns primitives → ¬ request.Blocks primitives ∧ ¬ request.Diverges primitives
  block_excludes_divergence : request.Blocks primitives → ¬ request.Diverges primitives

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation
