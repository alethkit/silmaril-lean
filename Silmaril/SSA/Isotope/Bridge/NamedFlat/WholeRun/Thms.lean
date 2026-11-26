module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.WholeRun.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.WholeRun

/-! # Finite execution from a named table to the typed packed dispatcher -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Region (Eval)
open LetCase.LocallyNameless (Tm)

universe u v

variable {V K F α : Type u} {n : Nat} [DecidableEq V] [DecidableEq K]
variable {prim : F → Value α → Part (Value α)} {env : Env α}
variable {exits : List K} {out : Nat} {value : Value α}

/-- A finite lexical exit, numbered in the external list, is equivalent to
finite Isotope evaluation of the elaborated table. In-flight payloads are
already shared tagged values and cross the boundary unchanged. -/
theorem run_iff {graph : CFG V K F} {captures : Fin n → V} {store : V → Value α}
    {target : FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (inputs : ∀ i : Fin n, env i.val = store (captures i)) :
    (out, value) ∈ (CFG.Cyclic.runSSA (model prim) graph store >>= numberExit exits) ↔
      Eval (instr prim) env target.erase () out value () :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.run_iff accepted inputs out value

variable {source : CFG V K F} {captures : Fin n → V} {store : V × Nat → Value α}
variable {target : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length n}

/-- Specialize finite agreement to the generated named lexical graph.
The accepted elaboration equation is carried by a successful `compileTyped`.
The name-to-environment agreement is at each capture's version-zero input. -/
theorem compile_run_iff (accepted : compile source exits captures = some target)
    (inputs : ∀ i : Fin n, env i.val = store (captures i, 0)) :
    (out, value) ∈ (CFG.Cyclic.runSSA (model prim) (CFG.Cyclic.Versioning.compile source) store >>=
      numberExit exits) ↔ Eval (instr prim) env target.erase () out value () :=
  run_iff accepted inputs

/-- Feed the actual elaborated graph through capture closure. Its packed
dispatcher exits at zero with the original payload injected at its first
external-list slot, under the state-preserving capture-packet contract. -/
theorem packed_run_iff {τ : Type v} [TypeFormers τ] [HasTy F τ] {β : BoundCtx τ n}
    {R : Fin (CFG.Cyclic.Versioning.compile source).blocks.length → τ}
    {E : Fin exits.length → τ} {input : Tm Empty F 0} {ambient : Env α}
    {closed : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length 0}
    (accepted : compile source exits captures = some target)
    (inputs : ∀ i : Fin n, env i.val = store (captures i, 0))
    (typed : closed.HasType .nil R E) (closure : Capture.Closes β input target closed)
    (packet : ∀ v state,
      LambdaSSA.Semantics.Tm.Eval (instr prim) ambient (Morphism.CaseSSA.erase input) () v state ↔
        v = Capture.packEnv n env ∧ state = ()) :
    (out, value) ∈ (CFG.Cyclic.runSSA (model prim) (CFG.Cyclic.Versioning.compile source) store >>=
      numberExit exits) ↔
      Eval (instr prim) ambient (FiniteCFG.packedExecutionRegion typed)
        () 0 (Region.packedExitValue out value) () :=
  (compile_run_iff accepted inputs).trans (Capture.packed_eval_at typed closure packet).symm

end Silmaril.Isotope.Bridge.NamedFlat
