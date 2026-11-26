module

public import Silmaril.SSA.PEG.Semantics.Defs
public import Silmaril.SSA.PEG.Scope
import Silmaril.Proofs.SSA.PEG.Semantics.Demand
import Silmaril.Proofs.SSA.PEG.Semantics.Equations
import Silmaril.Proofs.SSA.PEG.Semantics.Relabel
import Silmaril.Proofs.SSA.PEG.Semantics.Structural

public section

namespace Silmaril.SSA.PEG

open RVSDG (Tuple)

universe u v w x

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {Q : InstructionSet.{u,w} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l}

/-- Arbitrarily large selected counts and every prefix count are demands. -/
theorem Graph.sampleDemand {a b : Fin n} {loop : Fin l}
    (edge : g.Edge a (.sample loop) b) (i : Index l) (k : Nat) :
    g.Demand (b, i.set loop k) (a, i) :=
  ⟨.sample loop, edge, k, rfl⟩

/-- Soundness of the executable rank checker for the full, unbounded demand relation. -/
theorem Graph.demandWellFounded_of_check (g : Graph P params results n l) (rank : DemandRank n l)
    (check : rank.check g = true) : WellFounded g.Demand :=
  Semantics.Proofs.demand_wf_of_check g rank check

/-- Every infinite demand walk on a finite graph would eventually contain
only recurrent edges. The two cycle guards and well-founded loop ancestry
preclude an iteration coordinate decreasing infinitely often on that tail. -/
theorem Graph.demandWellFounded_of_cycles (g : Graph P params results n l)
    (forest : g.forest.WellFormed) (feedback : g.FeedbackCycles)
    (outerFeedback : g.OuterFeedbackCycles) : WellFounded g.Demand :=
  Semantics.Proofs.demand_wf_of_cycles forest feedback outerFeedback

theorem Graph.demandWellFounded (g : Graph P params results n l) (wf : g.WellFormed) :
    WellFounded g.Demand :=
  g.demandWellFounded_of_cycles wf.forest wf.feedback wf.outerFeedback

theorem monotonize_eq_some_iff {α : Type x} (s : Nat → Option α) (k : Nat) (value : α) :
    monotonize s k = some value ↔ s k = some value ∧ ∀ j < k, (s j).isSome :=
  Semantics.Proofs.monotonize_eq_some s k value

theorem firstTrue_eq_some_iff (s : Nat → Option Bool) (k : Nat) :
    firstTrue s = some k ↔ monotonize s k = some true ∧
      ∀ j < k, monotonize s j ≠ some true :=
  Semantics.Proofs.firstTrue_eq_some s k

theorem firstTrue_eq_none_iff (s : Nat → Option Bool) :
    firstTrue s = none ↔ ∀ j, monotonize s j ≠ some true :=
  Semantics.Proofs.firstTrue_eq_none s

variable (g) (m : Interpretation.{u,v,x} P) (env : Tuple m.Value params)

theorem Graph.denote_solves (wf : WellFounded g.Demand) : g.Solves m env (g.denote m env wf) :=
  Semantics.Proofs.denote_solves wf

theorem Graph.solves_unique (wf : WellFounded g.Demand) {a b : g.Valuation m}
    (ha : g.Solves m env a) (hb : g.Solves m env b) : a = b :=
  Semantics.Proofs.solves_unique wf ha hb

/-- Repaired Theorem 1. The simultaneous Figure 11 equations have exactly one
solution when the actual evaluation demands are well founded. -/
theorem Graph.existsUnique_solves (wf : WellFounded g.Demand) :
    ∃! values, g.Solves m env values :=
  Semantics.Proofs.existsUnique_solves wf

/-- Theorem 1 on the class admitted by the finite rank checker. -/
theorem Graph.existsUnique_solves_of_check (rank : DemandRank n l) (check : rank.check g = true) :
    ∃! values, g.Solves m env values :=
  g.existsUnique_solves m env (g.demandWellFounded_of_check rank check)

/-- Repaired Theorem 1 under the stronger structural guard. -/
theorem Graph.existsUnique_solves_of_wellFormed (wf : g.WellFormed) :
    ∃! values, g.Solves m env values :=
  g.existsUnique_solves m env (g.demandWellFounded wf)

theorem Graph.demand_mapOps (f : InstructionMap P Q) (p q : Request n l) :
    (g.mapOps f).Demand p q ↔ g.Demand p q :=
  Semantics.Proofs.demand_mapOps g f p q

theorem Graph.demandWellFounded_mapOps (f : InstructionMap P Q) :
    WellFounded (g.mapOps f).Demand ↔ WellFounded g.Demand :=
  ⟨Subrelation.wf (fun {p q} step => (g.demand_mapOps f p q).mpr step),
    Subrelation.wf (fun {p q} step => (g.demand_mapOps f p q).mp step)⟩

variable {model : Interpretation.{u,w,x} Q}

theorem Graph.equation_mapOps (f : InstructionMap P Q) (input : Tuple model.Value params)
    (values : g.Valuation (model.reduct f)) (q : Request n l) :
    (g.mapOps f).equation model input values q = g.equation (model.reduct f) input values q :=
  Semantics.Proofs.equation_mapOps f input values q

/-- Exact agreement at every node and index, including bottom. -/
theorem Graph.denote_mapOps (f : InstructionMap P Q) (input : Tuple model.Value params)
    (wf : WellFounded g.Demand) (mapped : WellFounded (g.mapOps f).Demand) :
    (g.mapOps f).denote model input mapped = g.denote (model.reduct f) input wf :=
  Semantics.Proofs.denote_mapOps f input wf mapped

theorem Graph.observe_denote_mapOps (f : InstructionMap P Q) (input : Tuple model.Value params)
    (wf : WellFounded g.Demand) (mapped : WellFounded (g.mapOps f).Demand) (i : Index l) :
    (g.mapOps f).observe model ((g.mapOps f).denote model input mapped) i =
      g.observe (model.reduct f) (g.denote (model.reduct f) input wf) i :=
  Semantics.Proofs.observe_denote_mapOps f input wf mapped i

end Silmaril.SSA.PEG
