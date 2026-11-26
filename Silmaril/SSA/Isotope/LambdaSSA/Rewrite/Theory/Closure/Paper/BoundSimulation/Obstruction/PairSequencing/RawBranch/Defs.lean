module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs

/-! # A visible primitive in literal branch position -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch

open Silmaril.Isotope.LambdaSSA
open Silmaril.Elgot.ITree
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (Primitive)

inductive Op where | call

instance : HasTy Op (Ty Empty) where
  src _ := .unit
  trg _ := .unit

instance : HasEff Op Bool where
  eff _ := true

/-- One call has a unit operand and a unit reply. -/
inductive Call : Type → Type where | request : Call Unit

def visiblePrim : Primitive Call Op Unit :=
  fun _ _ => vis .request (fun _ => pure .unit)

/-- Branch directly on a visible instruction. -/
abbrev rawBranch : Region Op := .br 0 (.op .call .unit)

theorem rawBranch_typed : HasType [] rawBranch [(Ty.unit : Ty Empty)] :=
  .br (ℓ := 0) rfl (.op .unit)

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch
