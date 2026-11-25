module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Linking

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink

open Continuation.Partial (Primitives)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {primitives : Primitives m σ}
variable {args outs : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
variable {unitId : Nat} {graph : Omega Op args outs sigs} {imports : Tuple m.Val args}
variable {store : σ}

/-- Every acyclic module link has a finite outcome under arbitrary partial actions. -/
theorem exists_outcome : ∃ outcome, Links primitives unitId graph imports store outcome :=
  Proofs.exists_outcome graph store

theorem outcome_unique {left right : Outcome m σ outs}
    (first : Links primitives unitId graph imports store left)
    (second : Links primitives unitId graph imports store right) : left = right :=
  Proofs.outcome_unique first second

/-- A failed initializer belongs to this unit, and its selected action
is undefined at the recorded inputs and store. -/
theorem undefined_action {failure : Failure m σ}
    (stopped : Links primitives unitId graph imports store (.undefined failure)) :
    failure.unitId = unitId ∧
      (∃ i : Fin sigs.length, failure.vertex = i.val ∧ IsDelta (graph.region.vertices i)) ∧
      (primitives.step failure.site.opcode failure.site.input).run failure.store = _root_.Part.none :=
  Proofs.undefined_action stopped

/-- The canonical total lift produces exactly the original exports
and preserves the initial ambient store. -/
theorem total_iff {outcome : Outcome m σ outs} :
    Links (Primitives.liftTotal m σ) unitId graph imports store outcome ↔
      outcome = .linked (Recursive.linkGraph m unitId graph imports) store :=
  Proofs.total_iff

/-- The unique finite link outcome. Arbitrary `Part` domains make this
classical. `Links` gives the finite evaluation rules directly. -/
noncomputable def link (primitives : Primitives m σ) (unitId : Nat) (graph : Omega Op args outs sigs)
    (imports : Tuple m.Val args) (store : σ) : Outcome m σ outs :=
  Classical.choose (exists_outcome (primitives := primitives) (unitId := unitId) (graph := graph)
    (imports := imports) (store := store))

theorem link_spec : Links primitives unitId graph imports store (link primitives unitId graph imports store) :=
  Classical.choose_spec exists_outcome

theorem link_total :
    link (Primitives.liftTotal m σ) unitId graph imports store =
      .linked (Recursive.linkGraph m unitId graph imports) store :=
  total_iff.mp link_spec

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink
