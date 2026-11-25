module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect

open Execution.Runtime (FuncAddr Frame TableInst)
open CallContinuation.OuterCall.Ranked.Graph (Program Function)

structure Site where
  table : TableInst
  typeIndex : TypeIdx
  signature : V1.FuncType

inductive Outcome where
  | bounds
  | null
  | mismatch (address : FuncAddr)
  | resolved (address : FuncAddr)
  deriving DecidableEq, Repr

/-- Table slot zero is shared by Lime1 and the Core Table32 profile. All
nonnull entries must name declarations in the checked graph. -/
def Site.check (site : Site) (program : Program) (caller : Frame) : Bool :=
  decide (caller.module.types[site.typeIndex.toNat]? = some site.signature) &&
    site.table.refs.all (fun entry => (entry.map fun a => (program.lookup a).isSome).getD true)

/-- The i32 selector is unsigned. Table lookup precedes the signature check.
A missing declaration lies outside the guard and has no outcome. -/
def Site.resolve (site : Site) (program : Program) (selector : BitVec 32) : Option Outcome :=
  match site.table.refs[selector.toNat]? with
  | none => some .bounds
  | some none => some .null
  | some (some address) => do
    let fn ← program.lookup address
    return if fn.declaration.type = site.signature then .resolved address else .mismatch address

inductive Resolution (site : Site) (program : Program) (selector : BitVec 32) : Outcome → Prop where
  | bounds (entry : site.table.refs[selector.toNat]? = none) : Resolution site program selector .bounds
  | null (entry : site.table.refs[selector.toNat]? = some none) : Resolution site program selector .null
  | mismatch {address : FuncAddr} {fn : Function}
      (entry : site.table.refs[selector.toNat]? = some (some address))
      (found : program.lookup address = some fn) (different : fn.declaration.type ≠ site.signature) :
      Resolution site program selector (.mismatch address)
  | resolved {address : FuncAddr} {fn : Function}
      (entry : site.table.refs[selector.toNat]? = some (some address))
      (found : program.lookup address = some fn) (same : fn.declaration.type = site.signature) :
      Resolution site program selector (.resolved address)

/-- Resolution stops at the first native trap or a pending successful call. -/
inductive Phase where
  | start
  | lookup
  | cast (entry : Option FuncAddr)
  | call (entry : Option FuncAddr)
  | boundsTrap
  | mismatchTrap
  | nullTrap
  deriving DecidableEq, Repr

/-- The remaining native action is still part of lookup, cast, or invocation.
The first trap is a separate phase. -/
def Phase.Pending : Phase → Prop
  | .start | .lookup | .cast _ | .call _ => True
  | _ => False

def Outcome.coreTrace (out : Outcome) : List Phase :=
  [.start, .lookup] ++ match out with
  | .bounds => [.boundsTrap]
  | .null => [.cast none, .call none, .nullTrap]
  | .mismatch addr => [.cast (some addr), .mismatchTrap]
  | .resolved addr => [.cast (some addr), .call (some addr)]

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
