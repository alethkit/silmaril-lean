module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Thms

/-! # Nested leaves preserve the original exit and token through both adapters -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Proofs

open Sequential
open Sequential.Flat.Serial (Agrees observe returns)
open Isotope.LambdaSSA (Region)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (carried carriedData point pack)
open OrderedRuntime.Structured (Instruction Data Threaded runtime RuntimeValues decode)
open NestedTheta.ExplicitRuntime (Checked)
open NestedTheta.ExplicitRuntime.Splice (append_denote)
open TwoBlock.TwoExit (ExitCode enter)
open Silmaril.Elgot (iter)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K M Q R X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private abbrev Values := RuntimeValues (TyDen (τ := τ)) σ

private theorem lift_primitive {ins outs : Ports (OrderedRuntime.Structured.Ty τ)}
    (i : Data ins) (o : Data outs) (op : Instruction (NestedFeedback.Pure τ) (NestedFeedback.Effect Φ) ins outs)
    (input : Tuple (Values (σ := σ)) (Threaded ins)) :
    (Wires.wireModel (ε := ε)).primitive (.ordered i o (Leaf.liftInstruction op)) input =
      (NestedFeedback.wireModel (ε := ε)).primitive (.ordered i o op) input := by
  cases op with | pure impossible => exact nomatch impossible | effect _ => rfl

private theorem lift_denote {args outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : NestedTheta.Term (NestedFeedback.Op Φ) (Threaded args) past sigs (Threaded outs)}
    (check : Checked (NestedFeedback.Pure τ) (NestedFeedback.Effect Φ) a b live t)
    (input : Tuple (Values (σ := σ)) (Threaded args))
    (locals : Locals (Values (σ := σ)) past) :
    (Leaf.liftChecked check).1.denoteOpenWith (Wires.wireModel (ε := ε)) input locals =
      t.denoteOpenWith (NestedFeedback.wireModel (ε := ε)) input locals := by
  induction check with
  | ret live wires => rfl
  | primitive live i o op wires rest ih =>
    simp only [Leaf.liftChecked, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
      NestedTheta.Node.ofBase, OrderedRuntime.Structured.primitiveNode, lift_primitive, ih]
    rfl
  | gamma extra selector live i o wires sigs checked rest inner outer =>
    simp only [Leaf.liftChecked, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
      NestedTheta.Node.ofBase, OrderedRuntime.Structured.gammaNode, Wires.read, Tuple.map, inner, outer]
    rfl
  | theta live i wires sigs checked rest inner outer =>
    simp only [Leaf.liftChecked, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
      NestedTheta.ExplicitRuntime.thetaNode, inner, outer]
    rfl

private theorem bridge_denote (op : Wires.Effect Φ (carried Q) (carried R)) (x : TyDen Q) (state : σ) :
    (Leaf.bridge op).1.denoteOpenWith (Wires.wireModel (ε := ε)) (point x state) PUnit.unit =
      (Wires.wireModel (ε := ε)).primitive (.ordered (carriedData Q) (carriedData R) (.effect op))
        (point x state) := by
  change ((Wires.wireModel (ε := ε)).primitive (.ordered (carriedData Q) (carriedData R) (.effect op))
    (point x state) >>= fun out => pure (point (out.get .head) (out.get (.tail .head)))) = _
  have eta (out : NestedFeedback.Point σ R) : point (out.get .head) (out.get (.tail .head)) = out := by
    cases out with
    | cons v tail =>
      cases tail with
      | cons token tail => cases tail; rfl
  simp only [eta, bind_pure]

private theorem bridge_enter (a : TyDen A) (state : σ) :
    (Leaf.bridge (Wires.Effect.enterNested (Φ := Φ) (A := A) (M := M))).1.denoteOpenWith
      (Wires.wireModel (ε := ε)) (point (enter a) state) PUnit.unit =
        Part.some (NestedFeedback.entryTuple (a, state)) := by
  rw [bridge_denote]
  change Part.map (decode (ts := carried (NestedFeedback.Carrier A M)))
    ((match TypeModel.coprodEquiv (ExitCode M M) A (enter a) with
      | .inl _ => StateT.mk fun _ => Part.none
      | .inr x => (pure (pack (NestedFeedback.start (D := M) x)) : StateT σ Part.{u} _)).run state) = _
  rw [enter, Equiv.apply_symm_apply]
  rfl

private theorem bridge_exit (out : LabelDen [M] × σ) :
    (Leaf.bridge (Wires.Effect.exitNested (Φ := Φ) (A := A) (M := M))).1.denoteOpenWith
      (Wires.wireModel (ε := ε)) (NestedFeedback.exitTuple out) PUnit.unit =
        Part.some (ExplicitRuntime.exitTuple (A := A) (D := M) (.inl (Sum.elim id PEmpty.elim out.1), out.2)) := by
  rcases out with ⟨(value | impossible), state⟩
  · change (Leaf.bridge (Wires.Effect.exitNested (Φ := Φ) (A := A) (M := M))).1.denoteOpenWith
      (Wires.wireModel (ε := ε)) (point (NestedFeedback.done value) state) PUnit.unit = _
    rw [bridge_denote]
    change Part.map (decode (ts := carried (Wires.First A M)))
      ((match TypeModel.coprodEquiv M A (NestedFeedback.done value) with
        | .inl x => (pure (pack (TwoBlock.TwoExit.finish (A := A) (C := M) (D := M) (.inl x))) : StateT σ Part.{u} _)
        | .inr _ => StateT.mk fun _ => Part.none).run state) = _
    rw [NestedFeedback.done, Equiv.apply_symm_apply]
    rfl
  · exact nomatch impossible

private theorem denote_congr {Γ labels : List τ} {p q : Region Φ} (eq : p = q)
    (hp : Region.HasType Γ p labels) (hq : Region.HasType Γ q labels) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) hp =
      Region.denote (ε := ε) (m := StateT σ Part.{u}) hq := by
  subst q
  rfl

theorem source_rounds (s : NestedFeedback.Loop Φ A B K M)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) (Leaf.source s).typing env =
      iter (NestedFeedback.round (ε := ε) s) env.2 >>= fun r => pure (Sum.inl r) := by
  rw [denote_congr (σ := σ) (ε := ε) (Leaf.source_region s) _ (NestedFeedback.regionTypingWithTail s [M])]
  exact NestedFeedback.denote_rounds_withTail s [M] coherent env

theorem leaf_agrees (s : NestedFeedback.Loop Φ A B K M)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) (Leaf.source s) (Leaf.code s).1.toGraph := by
  intro env initial
  have one := (NestedFeedback.Related.generated s).region_observe coherent env initial
  have body : (NestedFeedback.Wiring.loop s).1.denoteOpenWith (NestedFeedback.wireModel (ε := ε))
      (NestedFeedback.entryTuple (env.2, initial)) PUnit.unit =
      Part.map (NestedFeedback.exitTuple (A := A))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (NestedFeedback.regionTyping s) env).run initial) := by
    unfold NestedFeedback.observe NestedTheta.Partial.observe NestedFeedback.graph at one
    rwa [NestedTheta.Term.toTerm_toGraph] at one
  simp only [observe, NestedTheta.Partial.observe, NestedTheta.Term.toTerm_toGraph, Leaf.code, append_denote]
  rw [bridge_enter (Φ := Φ) (ε := ε)]
  simp only [Part.bind_eq_bind, Part.bind_some]
  rw [lift_denote, body, Part.bind_map]
  simp only [bridge_exit, Part.bind_some_eq_map]
  rw [source_rounds s coherent env, NestedFeedback.denote_rounds s coherent env]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some_eq_map, Part.map_map]
  rfl

theorem agrees (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) s.source s.graph := by
  induction s with
  | structured s => exact s.agrees coherent
  | nested s => exact leaf_agrees s coherent
  | link p q hp hq => exact Flat.Serial.splice_agrees p.code q.code hp hq coherent
  | branch gate p q k hp hq hk => exact StructuredCFG.branch_agrees gate p.code q.code k.code hp hq hk coherent

theorem returns_iff {src : Flat.Fragment Φ A E D} {g : Flat.Serial.Graph Φ A X Z L E D sigs}
    (h : Agrees (ε := ε) (σ := σ) src g) (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) src.typing env).run initial = Part.some (exit, final) := by
  rw [returns, ← NestedTheta.Partial.observe_eq_some]
  change observe (ε := ε) g env.2 initial = _ ↔ _
  rw [h env initial, Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  simp only [ExplicitRuntime.exitTuple_injective.eq_iff, exists_eq_right]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Proofs
