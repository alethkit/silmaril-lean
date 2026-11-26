module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree

/-! # Visible entry and transfer correspondence for named lexical tables -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive region)

universe u v

variable {E : Type u → Type u} {F : Type v} {V K α : Type (u + 1)}
  {n : Nat} [DecidableEq V] [DecidableEq K]

/-- The numbered named entry and the exact elaborated entry have equal weak
trees, with equal continuations for every reply. -/
theorem entry_tree (instr : Primitive E F α) (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (store : V → Value α) (env : Env α)
    (inputs : ∀ i : Fin n, env i.val = store (captures i)) :
    (graph.entry.evalJump (treeModel instr) store >>= fun p => pure (treeNumber (labelIndex graph.blocks exits) p)) =
      region instr env target.entry.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Interaction.entry_tree instr graph exits captures accepted store env inputs

/-- At a first-match table hit, one named lexical step has the same tree as
the selected Isotope block. Only its return is tagged as a continuation. -/
theorem step_tree (instr : Primitive E F α) (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (label : K) (i : Fin graph.blocks.length)
    (hit : graph.blocks.findFinIdx? (fun item => label == item.1) = some i)
    (store : V → Value α) (env : Env α) (payload : Value α) :
    (CFG.Cyclic.stepSSA (treeModel instr) graph.blocks store (label, payload) >>=
      fun s => pure (s.map id (treeNumber (labelIndex graph.blocks exits)))) =
      (region instr (extend env payload) (target.block i).erase >>= fun p => pure (.inr p)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Interaction.step_tree instr graph exits captures accepted
    label i hit store env payload

/-- The entry and step equations lift through the existing weak ITree
iterator. Numbering the named exit changes only the returned label. -/
theorem run_tree (instr : Primitive E F α) (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (store : V → Value α) (env : Env α) (inputs : ∀ i : Fin n, env i.val = store (captures i)) :
    (CFG.Cyclic.runSSA (treeModel instr) graph store >>= fun p => pure (treeExitNumber exits p)) =
      region instr env target.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Interaction.run_tree instr graph exits captures accepted store env inputs

/-- Specialize the weak tree equality to the named versioner's actual output.
A successful `compileTyped` supplies the exact accepted elaboration. -/
theorem compile_run_tree (instr : Primitive E F α) (source : CFG V K F)
    (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length n}
    (accepted : compile source exits captures = some target)
    (store : V × Nat → Value α) (env : Env α) (inputs : ∀ i : Fin n, env i.val = store (captures i, 0)) :
    (CFG.Cyclic.runSSA (treeModel instr) (CFG.Cyclic.Versioning.compile source) store >>=
      fun p => pure (treeExitNumber exits p)) = region instr env target.erase :=
  run_tree instr _ exits (fun i => (captures i, 0)) accepted store env inputs

end Silmaril.Isotope.Bridge.NamedFlat
