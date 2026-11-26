module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Thms

/-! A successful leading δ for numbered demand analysis. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered.Prefix (Table)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports : Ports (Ty V S)} {value : ValueSort V S}
variable {actions : Actions m σ} {unitId : Nat}
variable {inputsL inputsR : Tuple m.Val imports}
variable {init : DeltaTerm Op imports [] value} {initial : σ}

/-- The actual typed results of a leading δ and the common store needed
to compare the subsequent invocations. The initialized values can differ. -/
structure DeltaPrefix (actions : Actions m σ) (unitId : Nat)
    (init : DeltaTerm Op imports [] value) (inputsL inputsR : Tuple m.Val imports) (initial : σ) where
  left : Tuple m.Val [.value (.global value)]
  right : Tuple m.Val [.value (.global value)]
  store : σ
  linkedL : Executable.linkVertex (past := []) actions unitId inputsL PUnit.unit (.delta init.toGraph) initial = .linked left store
  linkedR : Executable.linkVertex (past := []) actions unitId inputsR PUnit.unit (.delta init.toGraph) initial = .linked right store

/-- Run the ordinary partial linker for both imports and check the common
post-link store. A blocked initializer or a store mismatch rejects the receipt. -/
def DeltaPrefix.check [DecidableEq σ] (actions : Actions m σ) (unitId : Nat)
    (init : DeltaTerm Op imports [] value) (inputsL inputsR : Tuple m.Val imports) (initial : σ) :
    Option (DeltaPrefix actions unitId init inputsL inputsR initial) :=
  match ranL : Executable.linkVertex (past := []) actions unitId inputsL PUnit.unit (.delta init.toGraph) initial,
      ranR : Executable.linkVertex (past := []) actions unitId inputsR PUnit.unit (.delta init.toGraph) initial with
  | .linked left storeL, .linked right storeR =>
    if same : storeR = storeL then
      some ⟨left, right, storeL, ranL, ranR.trans (congrArg (Outcome.linked right) same)⟩
    else none
  | _, _ => none

/-- Start the ordinary demand scope with the actual initialized row.
The δ contributes no checked callable slot. -/
def DeltaPrefix.scope (receipt : DeltaPrefix actions unitId init inputsL inputsR initial) : Scope m :=
  { Scope.ordinary m with
    past := [[.value (.global value)]]
    localsL := (receipt.left, PUnit.unit)
    localsR := (receipt.right, PUnit.unit) }

/-- No callable membership is manufactured for the initialized row.
Ordinary data remains available through the existing typed capture check. -/
def DeltaPrefix.checked (receipt : DeltaPrefix actions unitId init inputsL inputsR initial) :
    receipt.scope.Checked actions :=
  let start := Scope.Checked.ordinary actions
  ⟨⟨start.state.dispatch, Table.empty _ receipt.scope.localsL, Table.empty _ receipt.scope.localsR⟩,
    start.left, start.right⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
