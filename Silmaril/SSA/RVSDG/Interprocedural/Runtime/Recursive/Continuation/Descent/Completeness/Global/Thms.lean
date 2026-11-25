module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Extraction

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {final : Ports (Ty V S)}
variable {micro : Nat → State m final} {parent child : Point m final}

theorem ChildStep.live (edge : ChildStep micro parent child) : child.Live micro :=
  Proofs.child_live edge

theorem ChildStep.grows (edge : ChildStep micro parent child) :
    parent.index < child.index ∧ stackDepth parent.stack < stackDepth child.stack :=
  Proofs.child_grows edge

/-- Classify an actual infinite run at a root call. A return to the
empty stack would make the next step impossible. The result uses the
same deterministic machine with total, single-step primitives. -/
theorem classify_root {entry : Entry m} {micro : Nat → State m entry.results}
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (initial : micro 0 = entry.state .halt) :
    Classification entry micro :=
  Proofs.classify_root steps initial

/-- Apply the rooted classifier directly to a linked module's typed export. -/
theorem classify_linked (m : Machine.{u, v, w} Op) (unitId : Nat) {imports exports : Ports (Ty V S)}
    {sigs : List (Ports (Ty V S))} (graph : Omega Op imports exports sigs)
    (values : Tuple m.Val imports) {params results : Ports (Ty V S)}
    (port : Port exports (.value (.function params results))) (arguments : Tuple m.Val params)
    {micro : Nat → State m results} (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (initial : micro 0 = start (.call ((Recursive.linkGraph m unitId graph values).get port) arguments)) :
    Classification (linkedEntry m unitId graph values port arguments) micro :=
  classify_root steps initial

/-- Recover a single independent descent on the supplied microstep stream
at the original chain's entry positions. Choosing prefix witnesses uses
classical choice. -/
theorem chain_checkpoints {entry : Entry m} {micro : Nat → State m entry.results}
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (initial : micro 0 = entry.state .halt)
    (chain : InfiniteTrace (ChildStep micro) (Point.root entry)) :
    ∃ (run : Run m) (base : Stack m (run.entry 0).results entry.results) (positions : Nat → Nat),
      (run.entry 0).state base = entry.state .halt ∧ Checkpoints run base micro positions :=
  Proofs.chain_checkpoints steps initial chain

/-- The independent infinite-call certificate suffices to construct an
actual infinite run from the same root. -/
theorem calls_sound {entry : Entry m} (run : Run m) (base : Stack m (run.entry 0).results entry.results)
    (root : (run.entry 0).state base = entry.state .halt) : InfiniteTrace Step (entry.state .halt) :=
  root ▸ run.infinite base

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global
