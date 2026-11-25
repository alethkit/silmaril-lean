module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Observations.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (carried carriedData point)
open OrderedRuntime.Structured (RuntimeValues Threaded)
open TwoBlock.TwoExit (enter)
open NestedTheta.ExplicitRuntime.Splice (append_denote)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A I B K M C J E D : τ}

private abbrev Point (X : τ) :=
  Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried X))

private theorem repack {X : τ} (p : Point (σ := σ) X) :
    point (p.get .head) (p.get (.tail .head)) = p := by
  cases p with
  | cons x xs =>
    cases xs with
    | cons token tail => cases tail; rfl

private noncomputable def handoff (p : Point (σ := σ) (Wires.First I M)) :
    Part (Point (σ := σ) (Wires.Second M E D)) :=
  (Wires.wireModel (Φ := Φ) (ε := ε)).primitive
    (.ordered (carriedData _) (carriedData _) (.effect .link)) p

private theorem connector_denote (p : Point (σ := σ) (Wires.First I M)) :
    (connector (Φ := Φ) (E := E) (D := D)).1.denoteOpenWith (Wires.wireModel (ε := ε)) p PUnit.unit =
      handoff (Φ := Φ) (ε := ε) p := by
  change (handoff (Φ := Φ) (ε := ε) (σ := σ) (E := E) (D := D) (point (p.get .head) (p.get (.tail .head))) >>=
    fun q => pure (point (q.get .head) (q.get (.tail .head)))) = _
  simp only [repack, bind_pure]
  exact congrArg (handoff (Φ := Φ) (ε := ε) (E := E) (D := D)) (repack (σ := σ) p)

private theorem observe_join (producer : Producer Φ A I M) (consumer : Consumer Φ M E D)
    (input : TyDen A) (initial : σ) :
    observe (ε := ε) (join producer consumer) input initial =
      NestedTheta.Partial.observe (ExplicitRuntime.wireModel (ε := ε)) producer.1.toGraph (point input initial) >>=
        fun mid => handoff (Φ := Φ) (ε := ε) mid >>= NestedTheta.Partial.observe
          (ExplicitRuntime.wireModel (ε := ε)) consumer.1.toGraph := by
  simp only [observe, NestedTheta.Partial.observe, join, NestedTheta.Term.toTerm_toGraph, joinCode]
  rw [append_denote, Wires.lift_denote]
  congr 1
  funext mid
  rw [append_denote, connector_denote]
  congr 1
  funext next
  rw [NestedTheta.Partial.observe, NestedTheta.Term.toTerm_toGraph]
  exact Wires.lift_denote (ε := ε) (σ := σ) consumer.2 next PUnit.unit

theorem compile_after (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (input : TyDen A) (initial token : σ) (mid : LabelDen [M,M])
    (finished : Conditional.returns (ε := ε) (Conditional.graph p) input initial mid token) :
    observe (ε := ε) (compile p q) input initial =
      ExplicitRuntime.observe (ε := ε) (ExplicitRuntime.graph q) (merge mid) token := by
  have first : Conditional.observe (ε := ε) (Conditional.graph p) input initial =
      Part.some (ExplicitRuntime.exitTuple (A := I) (mid, token)) :=
    (NestedTheta.Partial.observe_eq_some _ _ _ _).mpr finished
  rw [compile, observe_join]
  change (Conditional.observe (ε := ε) (Conditional.graph p) input initial >>= fun result =>
    handoff (Φ := Φ) (ε := ε) result >>= NestedTheta.Partial.observe
      (ExplicitRuntime.wireModel (ε := ε)) (ExplicitRuntime.graph q)) = _
  rw [Part.bind_eq_bind, first, Part.bind_some]
  unfold handoff
  rw [Wires.link_boundary, Part.bind_eq_bind, Part.bind_some]
  rfl

theorem compile_no_producer (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (input : TyDen A) (initial : σ)
    (absent : Conditional.observe (ε := ε) (Conditional.graph p) input initial = Part.none) :
    observe (ε := ε) (compile p q) input initial = Part.none := by
  rw [compile, observe_join]
  change (Conditional.observe (ε := ε) (Conditional.graph p) input initial >>= _) = _
  rw [Part.bind_eq_bind, absent, Part.bind_none]

private theorem agree (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (producer : Producer Φ A I M) (consumer : Consumer Φ M E D)
    (hp : Conditional.graph p = producer.1.toGraph) (hq : ExplicitRuntime.graph q = consumer.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) (join producer consumer) env.2 initial =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Source p q).typing env).run initial) := by
  rw [observe_join producer consumer, ← hp, ← hq]
  change (Conditional.observe (ε := ε) (Conditional.graph p) env.2 initial >>= fun mid =>
    handoff (Φ := Φ) (ε := ε) mid >>= NestedTheta.Partial.observe
      (ExplicitRuntime.wireModel (ε := ε)) (ExplicitRuntime.graph q)) = _
  rw [(Conditional.Related.guarded p).region_observe coherent env initial,
    Flat.denote_link _ _ coherent, Flat.Fragment.guarded_denote, Flat.Fragment.loop_denote, StateT.run_bind]
  simp only [Part.bind_eq_bind, Part.bind_map, Part.map_bind]
  congr 1
  funext mid
  rcases mid with ⟨exit, token⟩
  unfold handoff
  rw [Wires.link_boundary, Part.bind_some]
  exact (ExplicitRuntime.Related.loop q).region_observe coherent (PUnit.unit, merge exit) token

theorem compile_observe (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) (compile p q) env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := M))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Source p q).typing env).run initial) :=
  agree p q _ _ rfl rfl coherent env initial

theorem recovered_observe {g : Graph Φ A I M E D} (w : Decomposition g B K C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := M))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.recover.typing env).run initial) := by
  have result := agree w.first.view.decode w.second.view.decode w.producer w.consumer
    w.first.wiring w.second.wiring coherent env initial
  rw [w.wiring] at result
  exact result

theorem returns_of_observe (g : Graph Φ A I M E D) (input : TyDen A) (initial final : σ)
    (exit : LabelDen [E,D]) (result : Part (LabelDen [E,D] × σ))
    (eq : observe (ε := ε) g input initial = Part.map (ExplicitRuntime.exitTuple (A := M)) result) :
    returns (ε := ε) g input initial exit final ↔ result = Part.some (exit, final) := by
  rw [returns, ← NestedTheta.Partial.observe_eq_some]
  change observe (ε := ε) g input initial = _ ↔ _
  rw [eq, Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  simp only [ExplicitRuntime.exitTuple_injective.eq_iff, exists_eq_right]

theorem map_none_iff {X Y : Type u} (f : X → Y) (v : Part X) :
    Part.map f v = Part.none ↔ v = Part.none := by
  rw [Part.eq_none_iff', Part.eq_none_iff']
  rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Proofs
