module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Refinement.Thms
public import Silmaril.Semantics.ITree.Trace.Thms

/-! # Finite trace refinement through effectful capture -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive Transfer region)
open Silmaril.Elgot.ITree (Tree TraceLE eq_iff_traceLE)
open LetCase.LocallyNameless (Tm)

universe u v w

variable {Events : Type u → Type u} {F : Type v} {V K α Reply : Type (u + 1)}
  {n : Nat} [DecidableEq V] [DecidableEq K]

/-- Pointwise inclusion of named observations at every produced capture value
implies inclusion at the accepted capture-free dispatcher. Each observed
return is numbered and tagged using the dispatcher's exit encoding. -/
theorem packed_run_tree_traceLE {τ : Type w} [TypeFormers τ] [HasTy F τ]
    {β : BoundCtx τ n}
    (instr : Primitive Events F α) (source : CFG V K F) (exits : List K) (captures : Fin n → V)
    {R : Fin (CFG.Cyclic.Versioning.compile source).blocks.length → τ}
    {L : Fin exits.length → τ}
    {target : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length n}
    {closed : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length 0}
    {input : Tm Empty F 0} {ambient : Env α} {original : Reply → Env α}
    {produce : Tree Events Reply} (store : Reply → V × Nat → Value α)
    (accepted : compile source exits captures = some target)
    (inputs : ∀ reply (i : Fin n), original reply i.val = store reply (captures i, 0))
    (typed : closed.HasType .nil R L) (closure : Capture.Closes β input target closed)
    (packet : LambdaSSA.Semantics.Interaction.term instr ambient (Morphism.CaseSSA.erase input) =
        (produce >>= fun reply => pure (Capture.packEnv n (original reply))))
    {spec : Reply → Tree Events (K × Value α)}
    (related : ∀ reply, TraceLE.{u, u+1} (CFG.Cyclic.runSSA (treeModel instr)
      (CFG.Cyclic.Versioning.compile source) (store reply)) (spec reply)) :
    TraceLE.{u, u+1} (region instr ambient (FiniteCFG.packedExecutionRegion typed))
      (produce >>= fun reply => spec reply >>= fun p =>
        pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) :=
  packed_run_tree_refines_of_mono instr source exits captures store accepted inputs typed closure packet
    (NamedRel := TraceLE.{u, u+1}) (PackedRel := TraceLE.{u, u+1})
    (fun h => TraceLE.bind_pure h _) (TraceLE.bind_right produce) related

/-- At the packed interface, mutual finite trace inclusion of the named
execution and a packed specification is equivalent to weak tree equality.
The two directions compare whole runs after the common capture producer and
the exact outward exit encoding. -/
theorem packed_run_tree_eq_iff_traceLE {τ : Type w} [TypeFormers τ] [HasTy F τ]
    {β : BoundCtx τ n}
    (instr : Primitive Events F α) (source : CFG V K F) (exits : List K) (captures : Fin n → V)
    {R : Fin (CFG.Cyclic.Versioning.compile source).blocks.length → τ}
    {L : Fin exits.length → τ}
    {target : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length n}
    {closed : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length 0}
    {input : Tm Empty F 0} {ambient : Env α} {original : Reply → Env α}
    {produce : Tree Events Reply} (store : Reply → V × Nat → Value α)
    (accepted : compile source exits captures = some target)
    (inputs : ∀ reply (i : Fin n), original reply i.val = store reply (captures i, 0))
    (typed : closed.HasType .nil R L) (closure : Capture.Closes β input target closed)
    (packet : LambdaSSA.Semantics.Interaction.term instr ambient (Morphism.CaseSSA.erase input) =
        (produce >>= fun reply => pure (Capture.packEnv n (original reply))))
    (spec : Tree Events (Transfer α)) :
    region instr ambient (FiniteCFG.packedExecutionRegion typed) = spec ↔
      let named := produce >>= fun reply => CFG.Cyclic.runSSA (treeModel instr)
        (CFG.Cyclic.Versioning.compile source) (store reply) >>= fun p =>
          pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))
      TraceLE.{u, u+1} named spec ∧ TraceLE.{u, u+1} spec named := by
  rw [packed_run_tree instr source exits captures store accepted inputs typed closure packet]
  exact eq_iff_traceLE

end Silmaril.Isotope.Bridge.NamedFlat
