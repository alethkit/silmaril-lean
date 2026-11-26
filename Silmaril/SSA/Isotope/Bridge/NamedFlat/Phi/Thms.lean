module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.WholeRun.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi

/-! # Finite φ execution through the named Isotope bridge -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Region (Eval)
open LetCase.LocallyNameless (Tm)

universe u v

variable {V K F α : Type u} {n : Nat} [DecidableEq V] [DecidableEq K]
variable {source : CFG.Cyclic.Phi.Graph V K F} {lexical : CFG (Option V × Nat) (Option K) F}
  {captures : Fin n → Option V × Nat} {target : FiniteCFG F lexical.blocks.length 1 n}
  {prim : F → Value α → Part (Value α)} {input : V → Value α} {env : Env α} {value : Value α}

/-- Finite returns of the independent φ semantics agree with the actual accepted
Isotope elaboration. The explicit return is the sole external label, at slot zero.
The φ and Isotope evaluators share a tagged value model and a partial primitive
implementation. Successful elaboration and agreement at every capture are required. -/
theorem run_iff (lowered : CFG.Cyclic.Phi.compile source = some lexical)
    (accepted : elaborate lexical [none] captures = some target)
    (inputs : ∀ i : Fin n, env i.val = CFG.Cyclic.Phi.inputEnv (model prim) input (captures i)) :
    (none, value) ∈ CFG.Cyclic.Phi.run (model prim) source input ↔
      Eval (instr prim) env target.erase () 0 value () :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.run_iff lowered accepted inputs

/-- Finite φ returns agree with the typed packed dispatcher. The capture producer
must return exactly the original capture record and preserve primitive state. The
sole external slot is injected at index zero in the packed return. -/
theorem packed_run_iff {τ : Type v} [TypeFormers τ] [HasTy F τ] {β : BoundCtx τ n}
    {R : Fin lexical.blocks.length → τ} {E : Fin 1 → τ} {packetInput : Tm Empty F 0}
    {ambient : Env α} {closed : FiniteCFG F lexical.blocks.length 1 0}
    (lowered : CFG.Cyclic.Phi.compile source = some lexical)
    (accepted : elaborate lexical [none] captures = some target)
    (inputs : ∀ i : Fin n, env i.val = CFG.Cyclic.Phi.inputEnv (model prim) input (captures i))
    (typed : closed.HasType .nil R E) (closure : Capture.Closes β packetInput target closed)
    (packet : ∀ v state,
      LambdaSSA.Semantics.Tm.Eval (instr prim) ambient (Morphism.CaseSSA.erase packetInput) () v state ↔
        v = Capture.packEnv n env ∧ state = ()) :
    (none, value) ∈ CFG.Cyclic.Phi.run (model prim) source input ↔
      Eval (instr prim) ambient (FiniteCFG.packedExecutionRegion typed)
        () 0 (Region.packedExitValue 0 value) () :=
  (run_iff lowered accepted inputs).trans (Capture.packed_eval_at typed closure packet).symm

end Silmaril.Isotope.Bridge.NamedFlat.Phi
