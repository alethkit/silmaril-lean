module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Infinite.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Divergence.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Infinite

/-! # Infinite internal execution from a named table to the packed dispatcher -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Diverges Env extend)
open LambdaSSA.Semantics.Region (Eval)
open LetCase.LocallyNameless (Tm)

universe u v w x

/-- Flat graphs with the same successful entry and internal transfers have
the same atomic divergence. Instruction signatures and capture contexts may differ. -/
theorem flat_diverges_iff_of_eval {F : Type v} {G : Type u} {α : Type w} {σ : Type x}
    {blocks exits n m : Nat} {target : FiniteCFG F blocks exits n} {other : FiniteCFG G blocks exits m}
    {env env' : Env α} {start : σ}
    {instr : F → Value α → σ → Value α → σ → Prop} {instr' : G → Value α → σ → Value α → σ → Prop}
    (entry : ∀ out value finish, Eval instr env target.entry.erase start out value finish ↔
      Eval instr' env' other.entry.erase start out value finish)
    (blocks : ∀ i current state out value finish,
      Eval instr (extend env current) (target.block i).erase state out value finish ↔
        Eval instr' (extend env' current) (other.block i).erase state out value finish) :
    Diverges instr (.region env target.erase start) ↔ Diverges instr' (.region env' other.erase start) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.flat_diverges_iff_of_eval entry blocks

/-- Capture closure transports infinite internal execution with the exact
state-preserving packet. Both the open and closed tables have flat bodies. -/
theorem Capture.diverges_iff {τ : Type u} {F : Type v} {α : Type w} {σ : Type x}
    {blocks exits n : Nat} {β : BoundCtx τ n} {input : Tm Empty F 0}
    {target : FiniteCFG F blocks exits n} {closed : FiniteCFG F blocks exits 0}
    {instr : F → Value α → σ → Value α → σ → Prop} {env ambient : Env α} {start : σ}
    (closure : Capture.Closes β input target closed)
    (packet : ∀ v state, LambdaSSA.Semantics.Tm.Eval instr ambient (Morphism.CaseSSA.erase input)
      start v state ↔ v = Capture.packEnv n env ∧ state = start) :
    Diverges instr (.region ambient closed.erase start) ↔ Diverges instr (.region env target.erase start) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.closure_diverges_iff closure packet

variable {V K F α : Type u} {n : Nat} [DecidableEq V] [DecidableEq K]
variable {prim : F → Value α → Part (Value α)} {env : Env α} {exits : List K}

/-- In the deterministic partial model, an explicit infinite path excludes a
finite result. Each transfer on a putative finite path must take the same
continuation as the infinite witness. -/
theorem InfiniteRun.runSSA_eq_none {graph : CFG V K F} {store : V → Value α}
    (infinite : InfiniteRun prim graph store) :
    CFG.Cyclic.runSSA (model prim) graph store = Part.none :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.runSSA_eq_none infinite

/-- Successful named internal transfers correspond in both directions to
Isotope divergence with atomic instructions and matching entry captures. -/
theorem infinite_run_iff {graph : CFG V K F} {captures : Fin n → V} {store : V → Value α}
    {target : FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (inputs : ∀ i : Fin n, env i.val = store (captures i)) :
    InfiniteRun prim graph store ↔ Diverges (instr prim) (.region env target.erase ()) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.infinite_run_iff accepted inputs

variable {source : CFG V K F} {captures : Fin n → V} {store : V × Nat → Value α}
variable {target : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length n}

/-- The compiler result carries the same correspondence, starting at the
version-zero captures used by the accepted Isotope graph. -/
theorem compile_infinite_run_iff (accepted : compile source exits captures = some target)
    (inputs : ∀ i : Fin n, env i.val = store (captures i, 0)) :
    InfiniteRun prim (CFG.Cyclic.Versioning.compile source) store ↔
      Diverges (instr prim) (.region env target.erase ()) :=
  infinite_run_iff accepted inputs

/-- A named infinite internal path is equivalent to the packed dispatcher's
may-divergence with atomic instructions. The capture producer's only finite
outcome must be the exact input packet with the same state. -/
theorem packed_infinite_run_iff {τ : Type v} [TypeFormers τ] [HasTy F τ] {β : BoundCtx τ n}
    {R : Fin (CFG.Cyclic.Versioning.compile source).blocks.length → τ}
    {E : Fin exits.length → τ} {input : Tm Empty F 0} {ambient : Env α}
    {closed : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length 0}
    (accepted : compile source exits captures = some target)
    (inputs : ∀ i : Fin n, env i.val = store (captures i, 0))
    (typed : closed.HasType .nil R E) (closure : Capture.Closes β input target closed)
    (packet : ∀ v state, LambdaSSA.Semantics.Tm.Eval (instr prim) ambient (Morphism.CaseSSA.erase input)
      () v state ↔ v = Capture.packEnv n env ∧ state = ()) :
    InfiniteRun prim (CFG.Cyclic.Versioning.compile source) store ↔
      Diverges (instr prim) (.region ambient (FiniteCFG.packedExecutionRegion typed) ()) :=
  (compile_infinite_run_iff accepted inputs).trans
    ((FiniteCFG.packedExecution_diverges_iff typed).trans (Capture.diverges_iff closure packet)).symm

end Silmaril.Isotope.Bridge.NamedFlat
