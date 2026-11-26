module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Defs

/-! # Weak interaction trees of the original φ evaluator -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi

open Silmaril.SSA.LambdaRTL
open Silmaril.Elgot.ITree (Tree)
open LambdaSSA.Semantics.Interaction (Primitive)

universe u v
variable {Events : Type u → Type u} {F : Type v} {V K α : Type (u + 1)}
  [DecidableEq V] [DecidableEq K]

/-- Run the predecessor-indexed source with shared visible primitive trees.
At a jump the source step reads the selected φ operands from the outgoing
predecessor store, then installs their results before executing the target.
Primitive replies affect the stored values threaded into later steps. -/
noncomputable def runTree (instr : Primitive Events F α)
    (source : CFG.Cyclic.Phi.Graph V K F) (input : V → Value α) :
    Tree Events (Option K × Value α) :=
  CFG.Cyclic.Phi.run (treeModel instr) source input

end Silmaril.Isotope.Bridge.NamedFlat.Phi
