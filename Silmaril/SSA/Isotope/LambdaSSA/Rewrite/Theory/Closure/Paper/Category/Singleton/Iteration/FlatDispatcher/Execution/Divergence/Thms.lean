module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDivergence

/-!
# May-divergence of the packed flat CFG

Finite successful instruction choices use the same transition relation in
both programs. An instruction may additionally diverge at a specified input
and state. The corresponding divergence judgments are existential and carry
no event trace or fairness condition.
-/

public section

universe u v w x

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open Silmaril.Isotope (Value)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {g : FiniteCFG Φ blocks exits 0}
  {α : Type w} {σ : Type x} {instr : Φ → Value α → σ → Value α → σ → Prop}
  {prim : Φ → Value α → σ → Prop} {env : Semantics.Env α} {start : σ}

/-- A divergent run is either an infinite sequence of internal transfers
or reaches a primitive certified divergent by `prim` in the entry or
a selected block. Both forms transport in both directions. -/
theorem packedExecution_external_diverges_iff (hg : HasType .nil R E g) :
    Semantics.External.Diverges instr prim (.region env (packedExecutionRegion hg) start) ↔
      Semantics.External.Diverges instr prim (.region env g.erase start) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution.packedExecution_external_diverges hg

/-- For atomic instructions the divergence judgment of these flat graphs
observes infinite internal transfers. -/
theorem packedExecution_diverges_iff (hg : HasType .nil R E g) :
    Semantics.Diverges instr (.region env (packedExecutionRegion hg) start) ↔
      Semantics.Diverges instr (.region env g.erase start) :=
  Semantics.External.Diverges.false_iff.symm.trans
    ((packedExecution_external_diverges_iff hg (prim := fun _ _ _ => False)).trans
      Semantics.External.Diverges.false_iff)

/-- The exact guarded singleton representative from `packedExecution_ofRegion`
has the same may-divergence after inserting the ignored input. -/
theorem packedExecution_representative_external_diverges_iff (hg : HasType .nil R E g)
    {dummy : Value α} :
    Semantics.External.Diverges instr prim
        (.region (Semantics.extend env dummy) ((packedExecutionRegion hg).renameVars Nat.succ) start) ↔
      Semantics.External.Diverges instr prim (.region env g.erase start) :=
  (Semantics.External.Diverges.renameVars_iff (fun _ => rfl)).trans (packedExecution_external_diverges_iff hg)

end Silmaril.Isotope.LambdaSSA.FiniteCFG
