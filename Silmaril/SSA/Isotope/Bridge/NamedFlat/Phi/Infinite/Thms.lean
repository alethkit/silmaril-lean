module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Infinite.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Infinite.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Infinite
import Silmaril.Semantics.Elgot.Thms

/-! # Atomic infinite execution of the predecessor-indexed φ bridge -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Diverges Env)
open LetCase.LocallyNameless (Tm)

universe u v

variable {V K F α : Type u} {n : Nat} [DecidableEq V] [DecidableEq K]
variable {source : CFG.Cyclic.Phi.Graph V K F} {lexical : CFG (Option V × Nat) (Option K) F}
  {captures : Fin n → Option V × Nat} {target : FiniteCFG F lexical.blocks.length 1 n}
  {prim : F → Value α → Part (Value α)} {input : V → Value α} {env : Env α}

/-- Checked φ lowering preserves and reflects a path of successful internal
transfers in the actual lexical evaluator. -/
theorem lexical_infinite_run_iff (lowered : CFG.Cyclic.Phi.compile source = some lexical) :
    CFG.Cyclic.Phi.InfiniteRun (model prim) source input ↔
      InfiniteRun prim lexical (CFG.Cyclic.Phi.inputEnv (model prim) input) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.lexical_infinite_run_iff lowered

/-- An infinite source path excludes a finite result in the shared partial model. -/
theorem run_eq_none_of_infinite (lowered : CFG.Cyclic.Phi.compile source = some lexical)
    (path : CFG.Cyclic.Phi.InfiniteRun (model prim) source input) :
    CFG.Cyclic.Phi.run (model prim) source input = Part.none := by
  rw [CFG.Cyclic.Phi.run_commutes lowered (model prim) ⟨fun _ _ => rfl⟩ input]
  exact ((lexical_infinite_run_iff lowered).mp path).runSSA_eq_none

/-- Infinite φ paths correspond to atomic Isotope divergence. The accepted
elaboration uses the single explicit exit and agrees at every entry capture.
Both evaluators use the same stateless partial primitive implementation. -/
theorem infinite_run_iff (lowered : CFG.Cyclic.Phi.compile source = some lexical)
    (accepted : elaborate lexical [none] captures = some target)
    (inputs : ∀ i : Fin n, env i.val = CFG.Cyclic.Phi.inputEnv (model prim) input (captures i)) :
    CFG.Cyclic.Phi.InfiniteRun (model prim) source input ↔ Diverges (instr prim) (.region env target.erase ()) :=
  (lexical_infinite_run_iff lowered).trans (NamedFlat.infinite_run_iff accepted inputs)

/-- The typed packed dispatcher's atomic may-divergence is equivalent to a
source path of successful transfers. The capture producer must return exactly
the entry record with unchanged state. -/
theorem packed_infinite_run_iff {τ : Type v} [TypeFormers τ] [HasTy F τ] {β : BoundCtx τ n}
    {R : Fin lexical.blocks.length → τ} {E : Fin 1 → τ} {packetInput : Tm Empty F 0}
    {ambient : Env α} {closed : FiniteCFG F lexical.blocks.length 1 0}
    (lowered : CFG.Cyclic.Phi.compile source = some lexical)
    (accepted : elaborate lexical [none] captures = some target)
    (inputs : ∀ i : Fin n, env i.val = CFG.Cyclic.Phi.inputEnv (model prim) input (captures i))
    (typed : closed.HasType .nil R E) (closure : Capture.Closes β packetInput target closed)
    (packet : ∀ v state, LambdaSSA.Semantics.Tm.Eval (instr prim) ambient
      (Morphism.CaseSSA.erase packetInput) () v state ↔ v = Capture.packEnv n env ∧ state = ()) :
    CFG.Cyclic.Phi.InfiniteRun (model prim) source input ↔
      Diverges (instr prim) (.region ambient (FiniteCFG.packedExecutionRegion typed) ()) :=
  (infinite_run_iff lowered accepted inputs).trans
    ((FiniteCFG.packedExecution_diverges_iff typed).trans (Capture.diverges_iff closure packet)).symm

end Silmaril.Isotope.Bridge.NamedFlat.Phi
