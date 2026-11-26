module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.ITree.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.ITree
import Silmaril.Semantics.ITree.Thms

/-! # Visible continuations of predecessor-indexed φ execution -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi

open Silmaril.SSA.LambdaRTL
open Silmaril.Elgot.ITree (Tree)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open LetCase.LocallyNameless (Tm)

universe u v w
variable {Events : Type u → Type u} {F : Type v} {V K α : Type (u + 1)}
  {n : Nat} [DecidableEq V] [DecidableEq K]
variable {source : CFG.Cyclic.Phi.Graph V K F} {lexical : CFG (Option V × Nat) (Option K) F}

/-- Entry preserves the whole tree when each pending source transfer is
encoded as a lexical packet. -/
theorem entry_tree (lowered : CFG.Cyclic.Phi.compile source = some lexical)
    (instr : Primitive Events F α) (input : V → Value α) :
    CFG.Cyclic.Phi.encode (treeModel instr) source <$>
        CFG.Cyclic.Phi.execute (treeModel instr) none source.entry input =
      lexical.entry.evalJump (treeModel instr) (CFG.Cyclic.Phi.inputEnv (treeModel instr) input) :=
  CFG.Cyclic.Phi.entry_commutes lowered (treeModel instr) ⟨fun _ _ => rfl⟩ input

/-- A source transfer and its encoded lexical transfer have identical weak
trees after mapping the next pending state. Primitive requests and every
reply continuation agree, including updates used by future φ operands. -/
theorem step_tree (lowered : CFG.Cyclic.Phi.compile source = some lexical)
    (instr : Primitive Events F α) (input : V → Value α) (current : CFG.Cyclic.Phi.Pending V K (Value α)) :
    Sum.map id (CFG.Cyclic.Phi.encode (treeModel instr) source) <$>
        CFG.Cyclic.Phi.step (treeModel instr) source current =
      CFG.Cyclic.stepSSA (treeModel instr) lexical.blocks (CFG.Cyclic.Phi.inputEnv (treeModel instr) input)
        (CFG.Cyclic.Phi.encode (treeModel instr) source current) :=
  CFG.Cyclic.Phi.step_commutes lowered (treeModel instr) ⟨fun _ _ => rfl⟩ input current

/-- The entry and continuation equations lift by weak-tree iteration. -/
theorem lexical_run_tree (lowered : CFG.Cyclic.Phi.compile source = some lexical)
    (instr : Primitive Events F α) (input : V → Value α) :
    runTree instr source input =
      CFG.Cyclic.runSSA (treeModel instr) lexical (CFG.Cyclic.Phi.inputEnv (treeModel instr) input) :=
  CFG.Cyclic.Phi.run_commutes lowered (treeModel instr) ⟨fun _ _ => rfl⟩ input

/-- Number the source's explicit return at the singleton external interface.
The elaboration must accept the actual lexical result, with matching captures. -/
theorem run_tree (lowered : CFG.Cyclic.Phi.compile source = some lexical)
    (instr : Primitive Events F α) (input : V → Value α) (captures : Fin n → Option V × Nat)
    {target : FiniteCFG F lexical.blocks.length 1 n}
    (accepted : elaborate lexical [none] captures = some target) (env : Env α)
    (inputs : ∀ i : Fin n, env i.val = CFG.Cyclic.Phi.inputEnv (treeModel instr) input (captures i)) :
    (runTree instr source input >>= fun p => pure (treeExitNumber [none] p)) = region instr env target.erase := by
  rw [lexical_run_tree lowered]
  exact NamedFlat.run_tree instr lexical [none] captures accepted _ env inputs

/-- The typed dispatcher runs the capture producer, then the original φ
runner for each reply. Only the eventual return is numbered and tagged.
The lowering premise is shape admission. Optional global SSA certification
can provide that equation through its own soundness theorem. -/
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
        pure (FiniteCFG.packedTreeOutput (treeExitNumber [none] p))) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Interaction.packed_run_tree
    instr captures store lowered accepted inputs typed closure packet

end Silmaril.Isotope.Bridge.NamedFlat.Phi
