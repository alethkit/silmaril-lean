module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

/-! # Observe the link and the two numbered θ vertices -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (carried carriedData pack point)
open OrderedRuntime.Structured (Data Threaded runtime runtimePort nextRuntime RuntimeValues Instruction)
open TwoBlock.TwoExit (Carrier Pure ExitCode enter finish)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)
open NestedTheta (stepWith)
open NestedTheta.ExplicitRuntime (Checked)
open LinearChain.Wiring (newest)
open Silmaril.Elgot (iter)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K M C J E D : τ}

private abbrev Values := RuntimeValues (TyDen (τ := τ)) σ
private abbrev Point (X : τ) := Tuple (Values (σ := σ)) (Threaded (carried X))

private theorem primitive_lift {ins outs : Ports (OrderedRuntime.Structured.Ty τ)}
    (i : Data ins) (o : Data outs) (op : Instruction (Pure τ) (ExplicitRuntime.Effect Φ) ins outs)
    (input : Tuple (Values (σ := σ)) (Threaded ins)) :
    (wireModel (ε := ε)).primitive (.ordered i o (liftInstruction op)) input =
      (ExplicitRuntime.wireModel (ε := ε)).primitive (.ordered i o op) input := by
  cases op <;> rfl

private theorem lifted {args outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : NestedTheta.Term (ExplicitRuntime.Op Φ) (Threaded args) past sigs (Threaded outs)}
    (check : Checked (Pure τ) (ExplicitRuntime.Effect Φ) a b live t)
    (input : Tuple (Values (σ := σ)) (Threaded args)) (locals : Locals (Values (σ := σ)) past) :
    (liftChecked check).1.denoteOpenWith (wireModel (ε := ε)) input locals =
      t.denoteOpenWith (ExplicitRuntime.wireModel (ε := ε)) input locals := by
  induction check with
  | ret live wires => rfl
  | primitive live i o op wires rest ih =>
    simp only [liftChecked, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
      NestedTheta.Node.ofBase, OrderedRuntime.Structured.primitiveNode, primitive_lift, ih]
    rfl
  | gamma extra selector live i o wires sigs checked rest inner outer =>
    simp only [liftChecked, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
      NestedTheta.Node.ofBase, OrderedRuntime.Structured.gammaNode, Wires.read, Tuple.map, inner, outer]
    rfl
  | theta live i wires sigs checked rest inner outer =>
    simp only [liftChecked, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
      NestedTheta.ExplicitRuntime.thetaNode, inner, outer]
    rfl

private theorem repack {X : τ} (p : Point (σ := σ) X) : point (p.get .head) (p.get (.tail .head)) = p := by
  cases p with
  | cons val tail =>
    cases tail with
    | cons token tail => cases tail; rfl

private noncomputable def loopAt (s : Loop Φ A B K E D) (x : Point (σ := σ) (Carrier A E D)) :
    Part (Point (σ := σ) (Carrier A E D)) :=
  iter (stepWith (fun input => (ExplicitRuntime.Wiring.thetaBody s).2.1.denoteOpenWith
    (ExplicitRuntime.wireModel (ε := ε)) input PUnit.unit)) x

private theorem loopAt_observe (s : Loop Φ A B K E D) (x : TyDen A) (token : σ) :
    loopAt (ε := ε) s (point (enter x) token) = ExplicitRuntime.observe (ε := ε) (ExplicitRuntime.graph s) x token := by
  unfold ExplicitRuntime.observe NestedTheta.Partial.observe ExplicitRuntime.graph
  rw [NestedTheta.Term.toTerm_toGraph]
  simp only [ExplicitRuntime.Wiring.loop, NestedTheta.Term.denoteOpenWith,
    NestedTheta.ExplicitRuntime.thetaNode, NestedTheta.Kind.denoteWith]
  change _ = loopAt (ε := ε) s (point (enter x) token) >>= fun p =>
    (pure (point (p.get .head) (p.get (.tail .head))) : Part _)
  simp only [repack, bind_pure]

private def linkAction (p : Point (σ := σ) (First A M)) : Part (Point (σ := σ) (Second M E D)) :=
  (wireModel (Φ := Φ) (ε := ε)).primitive
    (.ordered (carriedData (First A M)) (carriedData (Second M E D)) (.effect .link)) p

private theorem link_output (label : LabelDen [M,M]) (token : σ) :
    linkAction (Φ := Φ) (ε := ε) (E := E) (D := D) (ExplicitRuntime.exitTuple (A := A) (label, token)) =
      Part.some (point (enter (merge label)) token) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := SecondPorts M E D))
    ((match TypeModel.coprodEquiv (ExitCode M M) A (finish (A := A) (exitPayload label)) with
      | .inl e => (pure (pack (enter (A := M) (C := E) (D := D)
          (Sum.elim id id (TypeModel.coprodEquiv M M e)))) : StateT σ Part.{u} _)
      | .inr _ => StateT.mk fun _ => Part.none).run token) = _
  rw [finish, Equiv.apply_symm_apply]
  change Part.map (OrderedRuntime.Structured.decode (ts := SecondPorts M E D))
    (((pure (pack (enter (A := M) (C := E) (D := D)
      (Sum.elim id id (TypeModel.coprodEquiv M M ((TypeModel.coprodEquiv M M).symm (exitPayload label))))))) :
      StateT σ Part.{u} _).run token) = _
  rw [Equiv.apply_symm_apply]
  rcases label with x | x | impossible
  · rfl
  · rfl
  · exact nomatch impossible

private theorem observe_sequence (s : Loops Φ A B K M C J E D) (x : TyDen A) (token : σ) :
    observe (ε := ε) (graph s) x token =
      ExplicitRuntime.observe (ε := ε) (ExplicitRuntime.graph s.first) x token >>= fun p =>
        linkAction (Φ := Φ) (ε := ε) p >>= loopAt (ε := ε) s.second := by
  unfold observe NestedTheta.Partial.observe graph
  rw [NestedTheta.Term.toTerm_toGraph]
  simp only [code, NestedTheta.Term.denoteOpenWith, NestedTheta.ExplicitRuntime.thetaNode,
    NestedTheta.Node.ofBase, OrderedRuntime.Structured.primitiveNode, NestedTheta.Kind.denoteWith, lifted]
  change (loopAt (ε := ε) s.first (point (enter x) token) >>= fun a =>
    linkAction (Φ := Φ) (ε := ε) (σ := σ) (E := E) (D := D) (point (a.get .head) (a.get (.tail .head))) >>= fun b =>
      loopAt (ε := ε) (σ := σ) s.second (point (b.get .head) (b.get (.tail .head))) >>= fun c =>
        pure (point (c.get .head) (c.get (.tail .head)))) = _
  simp only [loopAt_observe]
  congr 1
  funext a
  rw [repack (σ := σ) (X := First A M) a]
  congr 1
  funext b
  rw [repack (σ := σ) (X := Second M E D) b]
  have ret : (fun c : Point (σ := σ) (Second M E D) =>
      (pure (point (c.get .head) (c.get (.tail .head))) : Part (Point (σ := σ) (Second M E D)))) = pure :=
    funext fun c => congrArg pure (repack (σ := σ) (X := Second M E D) c)
  rw [ret, bind_pure]

theorem graph_rounds (s : Loops Φ A B K M C J E D) (x : TyDen A) (token : σ) :
    observe (ε := ε) (graph s) x token =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        (((iter (ExplicitRuntime.round (ε := ε) (m := StateT σ Part.{u}) s.first) x) >>= fun mid =>
          iter (ExplicitRuntime.round (ε := ε) (m := StateT σ Part.{u}) s.second) (merge mid)).run token) := by
  rw [observe_sequence, ExplicitRuntime.graph_observe, StateT.run_bind]
  simp only [Part.bind_eq_bind, Part.bind_map, Part.map_bind]
  congr 1
  funext mid
  obtain ⟨label, state⟩ := mid
  rw [link_output, Part.bind_some, loopAt_observe, ExplicitRuntime.graph_observe]

theorem graph_observe (s : Loops Φ A B K M C J E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (token : σ) :
    observe (ε := ε) (graph s) env.2 token =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (regionTyping s) env).run token) := by
  rw [observe_sequence, region_sequential s coherent, StateT.run_bind]
  rw [(ExplicitRuntime.Related.loop s.first).region_observe coherent env token]
  simp only [Part.bind_eq_bind, Part.bind_map, Part.map_bind]
  congr 1
  funext mid
  obtain ⟨label, state⟩ := mid
  rw [link_output, Part.bind_some, loopAt_observe]
  exact (ExplicitRuntime.Related.loop s.second).region_observe coherent (PUnit.unit, merge label) state

theorem returns_of_observe {r : Isotope.LambdaSSA.Region Φ} {g : Graph Φ A M E D}
    (w : Related A B K M C J E D r g)
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ)
    (eq : observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := M))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial)) :
    returns (ε := ε) g env.2 initial label final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (label, final) := by
  rw [returns, ← NestedTheta.Partial.observe_eq_some]
  change observe (ε := ε) g env.2 initial = _ ↔ _
  rw [eq, Part.eq_some_iff, Part.eq_some_iff, Part.mem_map_iff]
  exact ⟨fun ⟨p, mem, same⟩ => ExplicitRuntime.exitTuple_injective same ▸ mem, fun mem => ⟨_, mem, rfl⟩⟩

theorem map_none_iff {P Q : Type u} (f : P → Q) (p : Part P) :
    Part.map f p = Part.none ↔ p = Part.none := by
  constructor
  · intro h
    rw [Part.eq_none_iff] at h ⊢
    intro x m
    exact h (f x) ((Part.mem_map_iff f).mpr ⟨x, m, rfl⟩)
  · rintro rfl
    exact Part.map_none f

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Proofs
