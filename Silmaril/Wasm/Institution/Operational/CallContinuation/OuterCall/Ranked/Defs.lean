module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked

open Execution.Runtime (FuncAddr)
open StraightLine
open DirectSequence.Enclosing.Framed

structure Entry where
  declaration : Declaration
  rank : Nat
  targets : List CallTarget

/-- Slots are indexed by runtime function address. An empty slot declares no target. -/
structure Table where
  entries : List (Option Entry)

def Table.lookup (table : Table) (address : FuncAddr) : Option Entry :=
  table.entries[address.value]?.join

def Table.rank (table : Table) (address : FuncAddr) : Nat :=
  ((table.lookup address).map Entry.rank).getD 0

def Table.checkTarget (table : Table) (entry : Entry) (target : CallTarget) : Bool :=
  match table.lookup target.address with
  | none => false
  | some callee =>
    decide (entry.declaration.module.funcs[target.index.toNat]? = some target.address) &&
    decide (callee.declaration = target.declaration) &&
    decide (callee.rank < entry.rank)

def Table.check (table : Table) : Bool :=
  table.entries.all fun
    | none => true
    | some entry => entry.targets.all (table.checkTarget entry)

/-- The table binds the address to the declaration and its complete list of direct targets. -/
def Table.Contains (table : Table) (address : FuncAddr) (decl : Declaration) (targets : List CallTarget) : Prop :=
  ∃ rank, table.lookup address = some ⟨decl, rank, targets⟩

/-- A direct edge with matching caller resolution and callee declaration. -/
def Table.Resolved (table : Table) (caller callee : FuncAddr) : Prop :=
  ∃ source target destination,
    table.lookup caller = some source ∧ target ∈ source.targets ∧ target.address = callee ∧
    source.declaration.module.funcs[target.index.toNat]? = some callee ∧
    table.lookup callee = some destination ∧ destination.declaration = target.declaration

def Table.checkEntry (table : Table) (address : FuncAddr) (decl : Declaration) (targets : List CallTarget) : Bool :=
  match table.lookup address with
  | none => false
  | some entry => decide (entry.declaration = decl ∧ entry.targets = targets)

abbrev Table.Nesting (table : Table) (calls : List FuncAddr) : Prop :=
  calls.IsChain table.Resolved

/-- A straight-line sequence targets the existing flat, numeric callee fragment. -/
def leafTarget (target : Sequence.Target) : CallTarget :=
  let fn := target.callee
  ⟨target.index, target.address, ⟨fn.module, fn.typeIndex, fn.params, fn.locals, fn.result.toList⟩⟩

/-- Match all the declared targets of the source body and its inner sequence.
Checking even unused slots keeps the certificate independent of the dynamic
arguments and the result of any particular execution. -/
def Table.checkInvocation (table : Table) (call : Source.Invocation) : Bool :=
  let inner := call.body.invocation.site.callTarget
  let suffix := call.body.targets.map leafTarget
  let leaves := call.body.invocation.site.targets.map leafTarget
  table.check &&
    (table.checkEntry call.target.address call.target.declaration (inner :: suffix) &&
      table.checkEntry inner.address inner.declaration leaves &&
      (leaves ++ suffix).all (fun t => table.checkEntry t.address t.declaration []))

def leafFrames {site : Sequence.Site} : Sequence.State site → List FuncAddr
  | .active i (.label ..) _ | .active i (.exit ..) _ => [(site.target i).address]
  | _ => []

/-- Entered function frames of the checked fragment, outermost first. The
surrounding caller is outside the fragment. Resolution has no frame yet,
and a completed invocation has already popped its frame. -/
def frames {call : Source.Invocation} : Source.State call → List FuncAddr
  | .call | .invoke | .framed (.done _) => []
  | .framed (.label (.active (.label q))) =>
      call.target.address :: call.body.invocation.site.address :: leafFrames q
  | .framed (.label (.active (.exit _))) =>
      [call.target.address, call.body.invocation.site.address]
  | .framed (.label (.continuation q)) => call.target.address :: leafFrames q
  | .framed _ => [call.target.address]

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked
