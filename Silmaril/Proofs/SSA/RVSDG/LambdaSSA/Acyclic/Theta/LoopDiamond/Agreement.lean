module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Proofs

open Sequential
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (carried carriedData results resultData point)
open OrderedRuntime.Structured (RuntimeValues Threaded decode)
open TwoBlock.TwoExit (ExitCode enter callCase exitLabel)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)
open NestedTheta.ExplicitRuntime.Splice (append_denote)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A M Y E D X I B K : τ}

private abbrev Point (X : τ) := Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried X))

private theorem repack (p : Point (σ := σ) X) :
    point (p.get .head) (p.get (.tail .head)) = p := by
  cases p with
  | cons x xs =>
    cases xs with
    | cons token tail => cases tail; rfl

private def handoff (p : Point (σ := σ) (Branch M I)) : Part (Point (σ := σ) (Result M E D)) :=
  (Wires.wireModel (Φ := Φ) (ε := ε)).primitive
    (.ordered (carriedData _) (carriedData _) (.effect .link)) p

private theorem connector (p : Point (σ := σ) (Branch M I)) :
    (Flat.Numbered.connector (Φ := Φ) (E := E) (D := D)).1.denoteOpenWith
        (Wires.wireModel (ε := ε)) p PUnit.unit =
      handoff (Φ := Φ) (ε := ε) p := by
  change (handoff (Φ := Φ) (ε := ε) (σ := σ) (E := E) (D := D) (point (p.get .head) (p.get (.tail .head))) >>=
    fun q => pure (point (q.get .head) (q.get (.tail .head)))) = _
  simp only [repack (σ := σ), bind_pure]

private theorem loopEval (s : Loop Φ I B K E D) (coherent : RegionCoherent
    (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (x : TyDen I) (token : σ) :
    (Wires.liftChecked (ExplicitRuntime.Wiring.loop s).2).1.denoteOpenWith
        (Wires.wireModel (ε := ε)) (point (enter x) token) PUnit.unit =
      Part.map (ExplicitRuntime.exitTuple (A := I))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Theta.regionTyping s) (PUnit.unit, x)).run token) := by
  rw [Wires.lift_denote]
  exact (congrArg (fun t => t.denoteOpenWith (ExplicitRuntime.wireModel (ε := ε))
    (point (enter x) token) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph (ExplicitRuntime.Wiring.loop s).1)).symm.trans
      ((ExplicitRuntime.Related.loop s).region_observe coherent (PUnit.unit, x) token)

private def joinPoint (p : LabelDen [M,M] × σ) : Point (σ := σ) (Result M E D) :=
  point (enter (merge p.1)) p.2

private theorem loopToJoin (s : Loop Φ I B K M M) (coherent : RegionCoherent
    (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (x : TyDen I) (token : σ) :
    ((Wires.liftChecked (ExplicitRuntime.Wiring.loop s).2).1.denoteOpenWith
      (Wires.wireModel (ε := ε)) (point (enter x) token) PUnit.unit >>= handoff (Φ := Φ) (ε := ε)) =
      Part.map (joinPoint (E := E) (D := D))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Theta.regionTyping s) (PUnit.unit,x)).run token) := by
  rw [loopEval s coherent, Part.bind_eq_bind, Part.bind_map, ← Part.bind_some_eq_map]
  congr 1
  funext out
  rcases out with ⟨label, state⟩
  exact Wires.link_boundary (Φ := Φ) (ε := ε) label state

private theorem leftEval (s : Diamond Φ A M Y E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (x : TyDen (ExitCode M M)) (token : σ) :
    (Wiring.left s).1.denoteOpenWith (Wires.wireModel (ε := ε))
        (point ((TypeModel.coprodEquiv (ExitCode M M) Y).symm (.inl x)) token) PUnit.unit =
      Part.map (joinPoint (E := E) (D := D))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Theta.regionTyping s.left)
          (PUnit.unit, Sum.elim id id (TypeModel.coprodEquiv M M x))).run token) := by
  simp only [Wiring.left, append_denote, connector, Part.bind_eq_bind, Part.bind_assoc]
  have hx : handoff (Φ := Φ) (ε := ε) (E := M) (D := M)
      (point ((TypeModel.coprodEquiv (ExitCode M M) Y).symm (.inl x)) token) =
      Part.some (point (enter (Sum.elim id id (TypeModel.coprodEquiv M M x))) token) := by
    let label := exitLabel (TypeModel.coprodEquiv M M x)
    have payload : exitPayload label = TypeModel.coprodEquiv M M x := by
      unfold label
      cases TypeModel.coprodEquiv M M x <;> rfl
    have merged : merge label = Sum.elim id id (TypeModel.coprodEquiv M M x) := by
      unfold label
      cases TypeModel.coprodEquiv M M x <;> rfl
    have packed : ExplicitRuntime.exitTuple (A := Y) (label, token) =
        point ((TypeModel.coprodEquiv (ExitCode M M) Y).symm (.inl x)) token := by
      unfold ExplicitRuntime.exitTuple TwoBlock.TwoExit.finish
      rw [payload, Equiv.symm_apply_apply]
    rw [← packed, handoff, Wires.link_boundary, merged]
  rw [hx, Part.bind_some]
  exact loopToJoin s.left coherent _ token

private theorem rightEval (s : Diamond Φ A M Y E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (x : TyDen Y) (token : σ) :
    (Wiring.right s).1.denoteOpenWith (Wires.wireModel (ε := ε)) (point (enter x) token) PUnit.unit =
      Part.map (joinPoint (E := E) (D := D))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Theta.regionTyping s.right) (PUnit.unit,x)).run token) := by
  simp only [Wiring.right, append_denote, connector]
  exact loopToJoin s.right coherent x token

private def classify (s : Diamond Φ A M Y E D) (x : TyDen A) (token : σ) :=
  (Wires.wireModel (Φ := Φ) (ε := ε)).primitive
    (.ordered (carriedData A) (resultData (Branch M Y)) (.effect (.loop (.acyclic (.classify .direct s.gate)))))
    (point x token)

private def gateResult (r : (TyDen (ExitCode M M) ⊕ TyDen Y) × σ) :
    Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (results (Branch M Y))) :=
  decode (ExplicitRuntime.choiceData r.1, r.2)

private theorem classify_eq (s : Diamond Φ A M Y E D) (x : TyDen A) (token : σ) :
    classify (ε := ε) s x token =
      Part.map gateResult
        ((callCase (ε := ε) (m := StateT σ Part.{u}) s.gate x).run token) := by
  change Part.map decode ((callCase (ε := ε) s.gate x >>= fun r =>
    (pure (ExplicitRuntime.choiceData r) : StateT σ Part.{u} _)).run token) = _
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map, Function.comp_def]
  rfl

private theorem selectEval (s : Diamond Φ A M Y E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (token : σ) :
    (Wiring.select s).1.denoteOpenWith (Wires.wireModel (ε := ε)) (point env.2 token) PUnit.unit =
      Part.map (joinPoint (E := E) (D := D))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u})
          (Flat.fork (.loop s.left) (.loop s.right) s.gate).typing env).run token) := by
  rw [Flat.denote_fork _ _ _ coherent, Flat.Fragment.loop_denote, Flat.Fragment.loop_denote,
    StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
  unfold Wiring.select
  rw [NestedTheta.Term.denoteOpenWith, Part.bind_eq_bind]
  change (classify (ε := ε) s env.2 token).bind _ = _
  rw [classify_eq, Part.bind_map]
  congr 1
  funext out
  rcases out with ⟨branch, state⟩
  cases branch with
  | inl x =>
    rw [NestedTheta.Term.denoteOpenWith, Part.bind_eq_bind]

    change ((Wiring.left s).1.denoteOpenWith (Wires.wireModel (ε := ε))
        (point ((TypeModel.coprodEquiv (ExitCode M M) Y).symm (.inl x)) state) PUnit.unit).bind
      (fun q => Part.some (point (q.get .head) (q.get (.tail .head)))) = _
    simp only [repack (σ := σ), Part.bind_some_right]
    exact leftEval s coherent x state
  | inr y =>
    rw [NestedTheta.Term.denoteOpenWith, Part.bind_eq_bind]
    change ((Wiring.right s).1.denoteOpenWith (Wires.wireModel (ε := ε)) (point (enter y) state) PUnit.unit).bind
      (fun q => Part.some (point (q.get .head) (q.get (.tail .head)))) = _
    simp only [repack (σ := σ), Part.bind_some_right]
    exact rightEval s coherent y state

theorem graph_observe (s : Diamond Φ A M Y E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (token : σ) :
    NestedTheta.Partial.observe (Wires.wireModel (ε := ε)) (graph s) (point env.2 token) =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (source s).typing env).run token) := by
  simp only [graph, NestedTheta.Partial.observe, NestedTheta.Term.toTerm_toGraph, Wiring.code]
  rw [append_denote, selectEval s coherent, source, Flat.denote_link _ _ coherent,
    Flat.Fragment.loop_denote, StateT.run_bind]
  simp only [Part.bind_eq_bind, Part.bind_map, Part.map_bind]
  congr 1
  funext out
  exact loopEval s.next coherent (merge out.1) out.2

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Proofs
