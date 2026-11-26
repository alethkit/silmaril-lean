module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms

/-! # Conditional refinement transport through effectful capture -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive Transfer region)
open Silmaril.Elgot.ITree (Tree)
open LetCase.LocallyNameless (Tm)

universe u v w

variable {Events : Type u → Type u} {F : Type v} {V K α Reply : Type (u + 1)}
  {n : Nat} [DecidableEq V] [DecidableEq K]

/-- A relation on named continuations transports to the packed dispatcher
when the exact exit encoding preserves the relation and the common producer
preserves pointwise related continuations. The capture premise holds at each
reply of the same producer on both sides. -/
theorem packed_run_tree_refines_of_mono {τ : Type w} [TypeFormers τ] [HasTy F τ]
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
    {NamedRel : Tree Events (K × Value α) → Tree Events (K × Value α) → Prop}
    {PackedRel : Tree Events (Transfer α) → Tree Events (Transfer α) → Prop}
    {spec : Reply → Tree Events (K × Value α)}
    (tag_mono : ∀ {a b}, NamedRel a b →
      PackedRel (a >>= fun p => pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p)))
        (b >>= fun p => pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))))
    (bind_mono : ∀ {a b : Reply → Tree Events (Transfer α)},
      (∀ reply, PackedRel (a reply) (b reply)) → PackedRel (produce >>= a) (produce >>= b))
    (related : ∀ reply, NamedRel (CFG.Cyclic.runSSA (treeModel instr)
      (CFG.Cyclic.Versioning.compile source) (store reply)) (spec reply)) :
    PackedRel (region instr ambient (FiniteCFG.packedExecutionRegion typed))
      (produce >>= fun reply => spec reply >>= fun p =>
        pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) := by
  rw [packed_run_tree instr source exits captures store accepted inputs typed closure packet]
  exact bind_mono (fun reply => tag_mono (related reply))

end Silmaril.Isotope.Bridge.NamedFlat
