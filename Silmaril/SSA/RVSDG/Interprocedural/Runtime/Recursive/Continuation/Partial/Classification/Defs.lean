module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Defs

/-! The independent outcomes of a partially interpreted linked invocation. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification

open CallDescent (Entry)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}

def Returns (primitives : Primitives m σ) (entry : Entry m σ) : Prop :=
  ∃ value store, Eval primitives entry.call.activation.job entry.store (.returned value store)

def Blocks (primitives : Primitives m σ) (entry : Entry m σ) : Prop :=
  ∃ (site : Site m) (pending : Descent.Pending m site.outs entry.call.results) (store : σ),
    Eval primitives entry.call.activation.job entry.store (.blocked site pending store)

/-- Exactly one of finite return, a finite selected undefined primitive,
and an independent divergence certificate holds for the invocation. -/
structure Trichotomy (primitives : Primitives m σ) (entry : Entry m σ) : Prop where
  exhaustive : Returns primitives entry ∨ Blocks primitives entry ∨ Divergence.Diverges primitives entry
  return_exclusive : Returns primitives entry → ¬ Blocks primitives entry ∧ ¬ Divergence.Diverges primitives entry
  block_excludes_divergence : Blocks primitives entry → ¬ Divergence.Diverges primitives entry

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification
