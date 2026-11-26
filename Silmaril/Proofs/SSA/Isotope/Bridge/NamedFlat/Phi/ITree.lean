module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.ITree.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Thms
import Silmaril.Semantics.ITree.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Interaction

open Silmaril.SSA.LambdaRTL Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat.Phi (runTree)
open Silmaril.Elgot.ITree (Tree)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open LetCase.LocallyNameless (Tm)

universe u v w
variable {Events : Type u → Type u} {F : Type v} {V K α : Type (u + 1)}
  {n : Nat} [DecidableEq V] [DecidableEq K]
variable {source : CFG.Cyclic.Phi.Graph V K F}

theorem packed_run_tree {τ : Type w} [TypeFormers τ] [HasTy F τ] {β : BoundCtx τ n}
    (instr : Primitive Events F α) (captures : Fin n → Option V)
    {R : Fin (CFG.Cyclic.Versioning.compile (CFG.Cyclic.Phi.lower source)).blocks.length → τ}
    {L : Fin 1 → τ}
    {target : FiniteCFG F (CFG.Cyclic.Versioning.compile (CFG.Cyclic.Phi.lower source)).blocks.length 1 n}
    {closed : FiniteCFG F (CFG.Cyclic.Versioning.compile (CFG.Cyclic.Phi.lower source)).blocks.length 1 0}
    {input : Tm Empty F 0} {ambient : Env α} {Reply : Type (u + 1)} {original : Reply → Env α}
    {produce : Tree Events Reply} (store : Reply → V → Value α)
    (lowered : CFG.Cyclic.Phi.compile source = some (CFG.Cyclic.Versioning.compile (CFG.Cyclic.Phi.lower source)))
    (accepted : NamedFlat.compile (CFG.Cyclic.Phi.lower source) [none] captures = some target)
    (inputs : ∀ reply (i : Fin n), original reply i.val =
      CFG.Cyclic.Phi.inputEnv (treeModel instr) (store reply) (captures i, 0))
    (typed : closed.HasType .nil R L) (closure : Capture.Closes β input target closed)
    (packet : LambdaSSA.Semantics.Interaction.term instr ambient (Morphism.CaseSSA.erase input) =
      (produce >>= fun reply => pure (Capture.packEnv n (original reply)))) :
    region instr ambient (FiniteCFG.packedExecutionRegion typed) =
      (produce >>= fun reply => runTree instr source (store reply) >>= fun p =>
        pure (FiniteCFG.packedTreeOutput (treeExitNumber [none] p))) := by
  rw [NamedFlat.packed_run_tree instr (CFG.Cyclic.Phi.lower source) [none] captures
    (fun reply => CFG.Cyclic.Phi.inputEnv (treeModel instr) (store reply))
    accepted inputs typed closure packet]
  apply congrArg (fun continuation => produce >>= continuation)
  funext reply
  unfold runTree
  rw [CFG.Cyclic.Phi.run_commutes lowered (treeModel instr) ⟨fun _ _ => rfl⟩ (store reply)]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Interaction
