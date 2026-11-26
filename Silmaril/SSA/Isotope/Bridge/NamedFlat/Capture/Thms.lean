module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Construction
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Semantics

/-! # Capture-free execution of the generated flat graph -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Capture

open LambdaSSA
open LambdaSSA.Semantics (Env)
open LetCase.LocallyNameless (Tm)

universe u v w x

variable {F : Type v} {blocks exits n : Nat}

/-- Close a typed graph, including the result of `NamedFlat.compileTyped`.
The input is a closed expression at the exact packed capture type. Reification
keeps every block at its original label with its original erased code. It
rejects blocks that use captures or fall outside the contracted body checker's
fragment. The entry uses the general typed product decoder. -/
def close {Base : Type u} [DecidableEq Base] [HasTy F (Ty Base)]
    (β : BoundCtx (Ty Base) n) (R : Fin blocks → Ty Base) (E : Fin exits → Ty Base)
    (g : FiniteCFG F blocks exits n) (hg : g.HasType β R E)
    (input : Tm Empty F 0)
    (typed : LetCase.LocallyNameless.HasType F .nil .nil input (Region.packedInputType β.toList)) :
    Option {closed : FiniteCFG F blocks exits 0 // closed.HasType .nil R E ∧ Closes β input g closed} :=
  match he : reify (g.entry.erase.packInputsDestructure β.toList) with
  | none => none
  | some entry =>
    match hb : tabulate blocks (fun i => reify (g.block i).erase) with
    | none => none
    | some table =>
      if ok : (List.finRange blocks).all
          (fun i => checkBody (SSA.FiniteSum.append R E) (.snoc .nil (R i)) (table i)) = true then
        some ⟨⟨.let₁ input entry, table⟩,
          by exact Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.close_sound β R E g hg input typed he hb ok⟩
      else none

variable {τ : Type u} {β : BoundCtx τ n}
  {g : FiniteCFG F blocks exits n} {closed : FiniteCFG F blocks exits 0} {input : Tm Empty F 0}
  {α : Type w} {σ : Type x} {instr : F → Value α → σ → Value α → σ → Prop}
  {original ambient : Env α} {start finish : σ} {out : Nat} {value : Value α}

/-- When the packet producer returns the original capture record with the same
primitive state, decoding it preserves and reflects entry evaluation. -/
theorem entry_eval_iff (h : Closes β input g closed)
    (packet : ∀ v state, Semantics.Tm.Eval instr ambient (Morphism.CaseSSA.erase input) start v state ↔
      v = packEnv n original ∧ state = start) :
    Semantics.Region.Eval instr ambient closed.entry.erase start out value finish ↔
      Semantics.Region.Eval instr original g.entry.erase start out value finish :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.entry_eval_iff h packet

/-- Entry preservation extends to every finite Isotope path. The blocks use
only the packet argument, so the original shared environment is unnecessary
after entry. -/
theorem graph_eval_iff (h : Closes β input g closed)
    (packet : ∀ v state, Semantics.Tm.Eval instr ambient (Morphism.CaseSSA.erase input) start v state ↔
      v = packEnv n original ∧ state = start) :
    Semantics.Region.Eval instr ambient closed.erase start out value finish ↔
      Semantics.Region.Eval instr original g.erase start out value finish :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.graph_eval_iff h packet

/-- The packed dispatcher and the original graph have the same finite exits at
the same primitive states, with the dispatcher exit encoded in its exact sum. -/
theorem packed_eval_at [TypeFormers τ] [HasTy F τ] {R : Fin blocks → τ} {E : Fin exits → τ}
    (typed : closed.HasType .nil R E) (h : Closes β input g closed)
    (packet : ∀ v state, Semantics.Tm.Eval instr ambient (Morphism.CaseSSA.erase input) start v state ↔
      v = packEnv n original ∧ state = start) :
    Semantics.Region.Eval instr ambient (FiniteCFG.packedExecutionRegion typed)
        start 0 (Region.packedExitValue out value) finish ↔
      Semantics.Region.Eval instr original g.erase start out value finish :=
  (FiniteCFG.packedExecution_eval_at typed).trans (graph_eval_iff h packet)

end Silmaril.Isotope.Bridge.NamedFlat.Capture
