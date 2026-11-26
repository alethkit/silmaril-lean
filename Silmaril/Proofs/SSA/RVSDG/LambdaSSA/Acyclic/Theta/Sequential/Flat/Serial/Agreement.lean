module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point carriedData)
open OrderedRuntime.Structured (RuntimeValues Threaded)
open TwoBlock.TwoExit (Carrier enter)
open NestedTheta.ExplicitRuntime.Splice (append_denote)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Y H M I J L E D B K : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private theorem connector_result (exit : LabelDen [M,M]) (token : σ) :
    (Numbered.connector (Φ := Φ) (I := H) (M := M) (E := I) (D := J)).1.denoteOpenWith
      (Wires.wireModel (ε := ε)) (ExplicitRuntime.exitTuple (A := H) (exit, token)) PUnit.unit =
        Part.some (point (enter (A := M) (C := I) (D := J) (merge exit)) token) := by
  change (Wires.wireModel (Φ := Φ) (ε := ε)).primitive
      (.ordered (carriedData (Wires.First H M)) (carriedData (Wires.Second M I J)) (.effect .link))
      (ExplicitRuntime.exitTuple (A := H) (exit, token)) >>= _ = _
  rw [Wires.link_boundary, Part.bind_eq_bind, Part.bind_some]
  rfl

private theorem splice_observe (p : Code Φ A X Y H M M ps) (q : Code Φ M I J L E D qs)
    (input : Tuple (RuntimeValues (TyDen (τ := τ)) σ) (WirePorts A X Y)) :
    NestedTheta.Partial.observe (Wires.wireModel (ε := ε)) (joinedGraph p q) input =
      NestedTheta.Partial.observe (Wires.wireModel (ε := ε)) p.1.toGraph input >>= fun mid =>
        (Numbered.connector (Φ := Φ) (I := H) (M := M) (E := I) (D := J)).1.denoteOpenWith
          (Wires.wireModel (ε := ε)) mid PUnit.unit >>=
          fun entry => NestedTheta.Partial.observe (Wires.wireModel (ε := ε)) q.1.toGraph entry := by
  simp only [joinedGraph, splice, NestedTheta.Partial.observe, NestedTheta.Term.toTerm_toGraph]
  rw [append_denote]
  congr 1
  funext mid
  exact append_denote (Wires.wireModel (ε := ε)) (Numbered.connector (I := H) (M := M) (E := I) (D := J)).2
    q.2 mid PUnit.unit

theorem splice_after (p : Code Φ A X Y H M M ps) (q : Code Φ M I J L E D qs)
    (input : TyDen A) (initial token : σ) (exit : LabelDen [M,M])
    (finished : observe (ε := ε) p.1.toGraph input initial =
      Part.some (ExplicitRuntime.exitTuple (A := H) (exit, token))) :
    observe (ε := ε) (joinedGraph p q) input initial = observe (ε := ε) q.1.toGraph (merge exit) token := by
  unfold observe at finished ⊢
  rw [splice_observe, Part.bind_eq_bind, finished, Part.bind_some, connector_result,
    Part.bind_eq_bind, Part.bind_some]

theorem splice_agrees (p : Code Φ A X Y H M M ps) (q : Code Φ M I J L E D qs)
    {left : Fragment Φ A M M} {right : Fragment Φ M E D}
    (hp : Agrees (ε := ε) (σ := σ) left p.1.toGraph) (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) (Flat.link left right) (joinedGraph p q) := by
  intro env initial
  have head := hp env initial
  unfold observe at head ⊢
  rw [splice_observe, head, Flat.denote_link _ _ coherent, StateT.run_bind]
  simp only [Part.bind_eq_bind, Part.bind_map, Part.map_bind]
  congr 1
  funext outcome
  obtain ⟨exit, token⟩ := outcome
  rw [connector_result, Part.bind_some]
  exact hq (PUnit.unit, merge exit) token

theorem loop_observe (s : Loop Φ A B K E D) (input : TyDen A) (initial : σ) :
    observe (ε := ε) (Spine.loop s).graph input initial =
      ExplicitRuntime.observe (ε := ε) (ExplicitRuntime.graph s) input initial := by
  simp only [observe, Spine.graph, Spine.code, ExplicitRuntime.observe, ExplicitRuntime.graph,
    NestedTheta.Partial.observe, NestedTheta.Term.toTerm_toGraph]
  exact Wires.lift_denote (ε := ε) (ExplicitRuntime.Wiring.loop s).2 (point (enter input) initial) PUnit.unit

private theorem loop_agrees (s : Loop Φ A B K E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) (Spine.loop s).source (Spine.loop s).graph := by
  intro env initial
  change observe (ε := ε) (Spine.loop s).graph env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := A))
    ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Fragment.loop s).typing env).run initial)
  rw [loop_observe, Fragment.loop_denote]
  exact (ExplicitRuntime.Related.loop s).region_observe coherent env initial

theorem spine_agrees (s : Spine Φ A X Y L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) s.source s.graph := by
  induction s with
  | loop s => exact loop_agrees s coherent
  | link p q hp hq => exact splice_agrees p.code q.code hp hq coherent

theorem returns_of_agrees {source : Fragment Φ A E D} {g : Graph Φ A X Y L E D sigs}
    (h : Agrees (ε := ε) (σ := σ) source g) (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) source.typing env).run initial = Part.some (exit, final) := by
  rw [returns, ← NestedTheta.Partial.observe_eq_some]
  change observe (ε := ε) g env.2 initial = _ ↔ _
  rw [h env initial, Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  simp only [ExplicitRuntime.exitTuple_injective.eq_iff, exists_eq_right]

theorem map_none_iff {X Y : Type u} (f : X → Y) (result : Part X) :
    Part.map f result = Part.none ↔ result = Part.none := by
  rw [Part.eq_none_iff', Part.eq_none_iff']
  rfl

theorem cut_returns {p : Code Φ A X Y H M M ps} {q : Code Φ M I J L E D qs}
    {g : Graph Φ A X Y L E D (Joined M I J ps qs)} (cut : Cut p q g)
    {left : Fragment Φ A M M} {right : Fragment Φ M E D}
    (hp : Agrees (ε := ε) (σ := σ) left p.1.toGraph) (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      ∃ (mid : LabelDen [M,M]) (token : σ), returns (ε := ε) p.1.toGraph env.2 initial mid token ∧
        returns (ε := ε) q.1.toGraph (merge mid) token exit final := by
  rw [← cut.wiring, returns_of_agrees (splice_agrees p q hp hq coherent) env,
    Flat.denote_link _ _ coherent, StateT.run_bind, Part.eq_some_iff, Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · rintro ⟨⟨mid, token⟩, before, after⟩
    exact ⟨mid, token, (returns_of_agrees hp env mid initial token).mpr (Part.eq_some_iff.mpr before),
      (returns_of_agrees hq (PUnit.unit, merge mid) exit token final).mpr (Part.eq_some_iff.mpr after)⟩
  · rintro ⟨mid, token, before, after⟩
    exact ⟨(mid, token), Part.eq_some_iff.mp ((returns_of_agrees hp env mid initial token).mp before),
      Part.eq_some_iff.mp ((returns_of_agrees hq (PUnit.unit, merge mid) exit token final).mp after)⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Proofs
