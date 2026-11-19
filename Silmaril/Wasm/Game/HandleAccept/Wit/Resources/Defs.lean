module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Resource.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Interp.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Resources

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

/-- The identity of a moved owning handle in the reference arena. The guest slot may be
reused and two identities may have the same representation. -/
structure Owned (resource : RtId) where
  identity : HandleObjId
  representation : Nat
  deriving DecidableEq, Repr

/-- The tree interpretation admits owners and does not provide any stored borrow values. -/
def treeEnv : WIT.Env Empty RtId :=
  { named := Empty.elim, own := Owned, borrow := fun _ => Empty, errorContext := Empty }

variable {E : CoreEngine} {World : Type}

/-- Retain the arena identity of the slot consumed by canonical `lift_own`. All type,
liveness and lending checks of `lift_own` still run. Its early removal and its trapping
effects belong to the component machine; this is not the Core checked import's preflight. -/
def take (limits : Component.Limits) (cx : LiftLowerContext E) (resource : RtId)
    (slot : Nat) : P E World ((WIT.ValType.own (Ref := Empty) resource).Interp treeEnv) :=
  liftOwnWith limits cx resource slot (Owned.mk (resource := resource))

inductive Call where
  | create (resource : RtId) (representation : Nat)
  | representation (resource : RtId) (slot : Nat)
  | drop (resource : RtId) (slot : Nat)

/-- Run the reference resource built-ins with the caller's actual destructor dispatcher. -/
def Call.program (limits : Component.Limits) (quirks : Quirks)
    (destructor : InstId → DtorRequest E → P E World Unit) : Call → P E World (List FlatValue)
  | .create resource rep => Builtins.resourceNew limits resource rep
  | .representation resource slot => Builtins.resourceRep limits resource slot
  | .drop resource slot => Builtins.resourceDrop limits quirks destructor resource slot

end Silmaril.Wasm.Game.HandleAccept.Wit.Resources
