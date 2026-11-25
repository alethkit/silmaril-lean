module

public import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms
import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

/-! # Finite graph observations for a single live token through a diamond -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedTheta (carried results pack point)
open OrderedRuntime.Structured
open Silmaril.Elgot (iter)
open NestedTheta (stepWith)
open TwoBlock.TwoExit (Carrier Route ExitCode Pure headerPorts armPorts routeResult callCase enter finish exitLabel)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B X Y K E D : τ}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev WireValues := RuntimeValues (TyDen (τ := τ)) σ
private abbrev Point (K : τ) := Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (carried K))
private abbrev Result (K : τ) := Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (results K))

private def armInput (saved : TyDen (Carrier A E D)) (route : TyDen (Route B E D)) (state : σ) :
    Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (armPorts A B E D)) :=
  .cons saved (.cons route (.cons state .nil))

private def rewire {K : τ} (out : Result (σ := σ) K) : Result (σ := σ) K :=
  .cons (out.get .head) (point (out.get (.tail .head)) (out.get (.tail (.tail .head))))

private theorem rewire_eq (out : Result (σ := σ) K) : rewire out = out := by
  cases out with
  | cons tag rest =>
    cases rest with
    | cons value rest =>
      cases rest with
      | cons token rest => cases rest; rfl

private theorem point_eq (out : Point (σ := σ) K) :
    point (out.get .head) (out.get (.tail .head)) = out := by
  cases out with
  | cons value rest =>
    cases rest with
    | cons token rest => cases rest; rfl

@[simp] private theorem fin_cases_one {F : Fin 2 → Sort*} (z : F 0) (s : (j : Fin 1) → F j.succ) :
    Fin.cases (motive := F) z s (1 : Fin 2) = s 0 :=
  Fin.cases_succ (motive := F) (0 : Fin 1)

private theorem primitive_map {ins out : Ports (OrderedRuntime.Structured.Ty τ)}
    (i : Data ins) (o : Data out) (op : Instruction (Pure τ) (Effect Φ) ins out)
    (payload : Tuple (Values (TyDen (τ := τ))) ins) (state : σ) :
    (wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive (.ordered i o op) (decode (payload, state)) =
      Part.map decode (((orderedModel (Φ := Φ) (ε := ε) (σ := σ)).step op payload).run state) := by
  simp only [wireModel, NestedTheta.ExplicitRuntime.Partial.wireModel, encode_decode]

private def headerTuple (p : (TyDen E ⊕ TyDen B) × σ) :
    Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (headerPorts B E D)) :=
  decode (routeResult (Sum.map (fun e => (TypeModel.coprodEquiv E D).symm (.inl e)) id p.1), p.2)

private def branchTuple (p : (TyDen X ⊕ TyDen Y) × σ) :
    Result (σ := σ) (Silmaril.coprod X Y) :=
  decode (branchResult p.1, p.2)

private def joinTuple (p : (TyDen D ⊕ TyDen A) × σ) : Result (σ := σ) (Carrier A E D) :=
  decode (LinearChain.lastResult p.1, p.2)

private def tagged (p : (LabelDen [E,D] ⊕ TyDen A) × σ) : Result (σ := σ) (Carrier A E D) :=
  TwoBlock.ExplicitRuntime.Skeleton.tagged (enter (A := A) (C := E) (D := D))
    (fun label => finish (A := A) (exitPayload label)) p

private theorem header_denote (s : Blocks Φ A B X Y K E D) (a : TyDen A) (state : σ) :
    (wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (OrderedTheta.carriedData _) (TwoBlock.ExplicitRuntime.Skeleton.headerData _) (.effect (.header s.header)))
      (point (enter a) state) =
      Part.map (headerTuple (D := D)) ((callCase (ε := ε) (m := StateT σ Part.{u}) s.header a).run state) := by
  change (wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive _ (decode (pack (enter a), state)) = _
  rw [primitive_map]
  change Part.map _ (((match TypeModel.coprodEquiv (ExitCode E D) A (enter a) with
    | .inl out => pure (routeResult (.inl out))
    | .inr a => callCase (ε := ε) s.header a >>= fun xy =>
        pure (routeResult (Sum.map (fun e => (TypeModel.coprodEquiv E D).symm (.inl e)) id xy))) :
      StateT σ Part.{u} _).run state) = _
  rw [enter, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some_eq_map,
    Part.map_map]
  rfl

private theorem classifier_denote (s : Blocks Φ A B X Y K E D) (saved : TyDen (Carrier A E D))
    (b : TyDen B) (state : σ) :
    (wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (.value (.value .nil)) (.control (.value .nil)) (.effect (.classifier s.diamond.classifier)))
      (armInput saved (LinearChain.bodyRoute b) state) =
      Part.map branchTuple ((callCase (ε := ε) (m := StateT σ Part.{u}) s.diamond.classifier b).run state) := by
  change (wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive _
    (decode (ts := armPorts A B E D) (.cons saved (pack (LinearChain.bodyRoute b)), state)) = _
  rw [primitive_map]
  change Part.map _ (((match TypeModel.coprodEquiv (ExitCode E D) B (LinearChain.bodyRoute b) with
    | .inl _ => StateT.mk fun _ => Part.none
    | .inr b => callCase (ε := ε) s.diamond.classifier b >>= fun xy => pure (branchResult xy)) :
      StateT σ Part.{u} _).run state) = _
  rw [LinearChain.bodyRoute, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some_eq_map,
    Part.map_map]
  rfl

private theorem arm_denote (op : Effect Φ (branchArgs X Y) (carried K))
    (payload : TyDen (Silmaril.coprod X Y)) (state : σ) :
    (Wiring.arm op).1.denoteOpenWith (wireModel (Φ := Φ) (ε := ε) (σ := σ))
        (point payload state) PUnit.unit =
      Part.map (decode (ts := carried K))
        (((orderedModel (Φ := Φ) (ε := ε) (σ := σ)).effect op (pack payload)).run state) := by
  change ((wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
    (.ordered (OrderedTheta.carriedData _) (OrderedTheta.carriedData K) (.effect op))
    (decode (pack payload, state)) >>= fun output =>
      pure (point (output.get .head) (output.get (.tail .head)))) = _
  rw [primitive_map]
  change (Part.map _ _ >>= fun (output : Point (σ := σ) K) =>
    pure (point (output.get .head) (output.get (.tail .head)))) = _
  simp only [point_eq, bind_pure]
  rfl

private theorem chosenArm_denote (s : Branches Φ B X Y K) (p : (TyDen X ⊕ TyDen Y) × σ) :
    (Wiring.diamondArms s ((branchTuple p).get .head).down).1.denoteOpenWith
      (wireModel (Φ := Φ) (ε := ε) (σ := σ))
      (point ((branchTuple p).get (.tail .head)) ((branchTuple p).get (.tail (.tail .head)))) PUnit.unit =
        Part.map (fun p => point p.1 p.2) (((runArm (ε := ε) (m := StateT σ Part.{u}) s p.1).run p.2)) := by
  rcases p with ⟨x | y, state⟩
  · change (Wiring.arm (.left s.left)).1.denoteOpenWith (wireModel (Φ := Φ) (ε := ε) (σ := σ))
      (point ((TypeModel.coprodEquiv X Y).symm (.inl x)) state) PUnit.unit = _
    rw [arm_denote]
    change Part.map _ (((match TypeModel.coprodEquiv X Y ((TypeModel.coprodEquiv X Y).symm (.inl x)) with
      | .inl x => TwoBlock.call (ε := ε) s.left x >>= fun k => pure (pack k)
      | .inr _ => StateT.mk fun _ => Part.none) : StateT σ Part.{u} _).run state) = _
    rw [Equiv.apply_symm_apply]
    simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
      Part.bind_some_eq_map, Part.map_map]
    rfl
  · change (Wiring.arm (.right s.right)).1.denoteOpenWith (wireModel (Φ := Φ) (ε := ε) (σ := σ))
      (point ((TypeModel.coprodEquiv X Y).symm (.inr y)) state) PUnit.unit = _
    rw [arm_denote]
    change Part.map _ (((match TypeModel.coprodEquiv X Y ((TypeModel.coprodEquiv X Y).symm (.inr y)) with
      | .inl _ => StateT.mk fun _ => Part.none
      | .inr y => TwoBlock.call (ε := ε) s.right y >>= fun k => pure (pack k)) : StateT σ Part.{u} _).run state) = _
    rw [Equiv.apply_symm_apply]
    simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
      Part.bind_some_eq_map, Part.map_map]
    rfl

private theorem join_denote (s : Blocks Φ A B X Y K E D) (k : TyDen K) (state : σ) :
    (wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (OrderedTheta.carriedData K) (OrderedTheta.resultData (Carrier A E D)) (.effect (.join s.join)))
      (point k state) =
        Part.map (joinTuple (E := E)) ((callCase (ε := ε) (m := StateT σ Part.{u}) s.join k).run state) := by
  change (wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive _ (decode (pack k, state)) = _
  rw [primitive_map]
  change Part.map _ ((callCase (ε := ε) (m := StateT σ Part.{u}) s.join k >>=
    fun xy => pure (LinearChain.lastResult xy)).run state) = _
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

private theorem bodyArm_denote (s : Blocks Φ A B X Y K E D) (saved : TyDen (Carrier A E D))
    (b : TyDen B) (state : σ) :
    (Wiring.bodyArm s).1.denoteOpenWith (wireModel (Φ := Φ) (ε := ε) (σ := σ))
        (armInput saved (LinearChain.bodyRoute b) state) PUnit.unit =
      Part.map joinTuple ((bodyAction (ε := ε) (m := StateT σ Part.{u}) s b).run state) := by
  change ((wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (.value (.value .nil)) (.control (.value .nil)) (.effect (.classifier s.diamond.classifier)))
      (armInput saved (LinearChain.bodyRoute b) state) >>= fun out =>
    (Wiring.diamondArms s.diamond (out.get .head).down).1.denoteOpenWith
      (wireModel (Φ := Φ) (ε := ε) (σ := σ)) (point (out.get (.tail .head)) (out.get (.tail (.tail .head))))
      PUnit.unit >>= fun k =>
    (wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (OrderedTheta.carriedData K) (OrderedTheta.resultData (Carrier A E D)) (.effect (.join s.join)))
      (point (k.get .head) (k.get (.tail .head))) >>= fun result => pure (rewire result)) = _
  simp only [rewire_eq, classifier_denote, bodyAction, StateT.run_bind, Part.bind_eq_bind,
    Part.bind_map, Part.map_bind]
  congr 1
  funext p
  rw [chosenArm_denote s.diamond p, Part.bind_map]
  congr 1
  funext k
  change ((wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
    (.ordered (OrderedTheta.carriedData K) (OrderedTheta.resultData (Carrier A E D)) (.effect (.join s.join)))
    (point k.1 k.2) >>= pure) = _
  rw [bind_pure]
  exact join_denote (ε := ε) (σ := σ) s k.1 k.2

private theorem outer_exit (s : Blocks Φ A B X Y K E D) (saved : TyDen (Carrier A E D))
    (e : TyDen E) (state : σ) :
    (Wiring.outerArms s 0).1.denoteOpenWith (wireModel (Φ := Φ) (ε := ε) (σ := σ))
      (armInput (B := B) saved ((TypeModel.coprodEquiv (ExitCode E D) B).symm
        (.inl ((TypeModel.coprodEquiv E D).symm (.inl e)))) state) PUnit.unit =
      Part.some (tagged (A := A) (D := D) (.inl (.inl e), state)) := by
  change (TwoBlock.ExplicitRuntime.Skeleton.arm (.pure (Pure.exit (A := A) (B := B) (C := E) (D := D)))).1.denoteOpenWith
    (wireModel (Φ := Φ) (ε := ε) (σ := σ)) _ PUnit.unit = _
  change ((wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
    (.ordered (.value (.value .nil)) (OrderedTheta.resultData _)
      (.pure (Pure.exit (A := A) (B := B) (C := E) (D := D))))
    (decode (ts := armPorts A B E D) (.cons saved (pack ((TypeModel.coprodEquiv (ExitCode E D) B).symm
      (.inl ((TypeModel.coprodEquiv E D).symm (.inl e))))), state)) >>= fun out => pure (rewire out)) = _
  rw [primitive_map]
  simp only [rewire_eq, bind_pure]
  change Part.map _ (Part.some
    ((match TypeModel.coprodEquiv (ExitCode E D) B ((TypeModel.coprodEquiv (ExitCode E D) B).symm
        (.inl ((TypeModel.coprodEquiv E D).symm (.inl e)))) with
      | .inl out => OrderedTheta.packChoice (.inl ((TypeModel.coprodEquiv (ExitCode E D) A).symm (.inl out)))
      | .inr _ => OrderedTheta.packChoice (.inr saved)), state)) = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem thetaBody_denote (s : Blocks Φ A B X Y K E D) (a : TyDen A) (state : σ) :
    (Wiring.thetaBody s).1.denoteOpenWith
        (wireModel (Φ := Φ) (ε := ε) (σ := σ)) (point (enter a) state) PUnit.unit =
      Part.map tagged ((round (ε := ε) (m := StateT σ Part.{u}) s a).run state) := by
  change ((wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (OrderedTheta.carriedData _) (TwoBlock.ExplicitRuntime.Skeleton.headerData _) (.effect (.header s.header)))
      (point (enter a) state) >>= fun output =>
    (Wiring.outerArms s (output.get .head).down).1.denoteOpenWith (wireModel (Φ := Φ) (ε := ε) (σ := σ))
      (armInput (enter a) (output.get (.tail .head)) (output.get (.tail (.tail .head)))) PUnit.unit >>=
    fun result => pure (rewire result)) = _
  simp only [rewire_eq, header_denote, round, StateT.run_bind, Part.bind_eq_bind,
    Part.pure_eq_some, Part.bind_some_right, Part.bind_map, Part.map_bind]
  congr 1
  funext p
  obtain ⟨result, token⟩ := p
  cases result with
  | inl e =>
    change (Wiring.outerArms s 0).1.denoteOpenWith (wireModel (Φ := Φ) (ε := ε) (σ := σ))
      (armInput (enter a) ((TypeModel.coprodEquiv (ExitCode E D) B).symm
        (.inl ((TypeModel.coprodEquiv E D).symm (.inl e)))) token) PUnit.unit = _
    rw [outer_exit]
    rfl
  | inr b =>
    change (Wiring.bodyArm s).1.denoteOpenWith (wireModel (Φ := Φ) (ε := ε) (σ := σ))
      (armInput (enter a) (LinearChain.bodyRoute b) token) PUnit.unit = _
    rw [bodyArm_denote]
    simp only [StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
    rw [← Part.bind_some_eq_map]
    congr 1
    funext p
    rcases p with ⟨(d | a), token⟩ <;> rfl

private def entry (p : TyDen A × σ) : Point (σ := σ) (Carrier A E D) :=
  point (enter p.1) p.2

private def complete (p : LabelDen [E,D] × σ) : Point (σ := σ) (Carrier A E D) :=
  point (finish (exitPayload p.1)) p.2

private noncomputable def wireBody (s : Blocks Φ A B X Y K E D) (input : Point (σ := σ) (Carrier A E D)) :=
  (Wiring.thetaBody s).1.denoteOpenWith
    (wireModel (Φ := Φ) (ε := ε) (σ := σ)) input PUnit.unit

private theorem step_denote (s : Blocks Φ A B X Y K E D) (input : TyDen A × σ) :
    stepWith (wireBody (ε := ε) s) (entry input) =
      Silmaril.Elgot.StateT.body (round (ε := ε) (m := StateT σ Part.{u}) s) input >>= fun result =>
        pure (Sum.map complete entry result) := by
  change stepWith (wireBody (ε := ε) s) (point (enter input.1) input.2) = _
  unfold stepWith
  rw [Bind.kleisliRight]
  change (wireBody (ε := ε) s (point (enter input.1) input.2) >>= _) = _
  unfold wireBody
  rw [thetaBody_denote]
  simp only [Silmaril.Elgot.StateT.body, Part.bind_eq_bind, Part.bind_map, Part.bind_assoc]
  congr 1
  funext p
  rcases p with ⟨(out | next), state⟩ <;>
    simp only [Function.comp_apply, Part.pure_eq_some, Part.bind_some] <;> rfl

private theorem wire_iterates (s : Blocks Φ A B X Y K E D) (a : TyDen A) (state : σ) :
    NestedTheta.Partial.observe (wireModel (Φ := Φ) (ε := ε) (σ := σ)) (graph s) (point (enter a) state) =
      Part.map (complete (A := A)) ((iter (round (ε := ε) (m := StateT σ Part.{u}) s) a).run state) := by
  let step := stepWith (wireBody (ε := ε) (σ := σ) s)
  have normalized :
      NestedTheta.Partial.observe (wireModel (Φ := Φ) (ε := ε) (σ := σ)) (graph s) (point (enter a) state) =
        iter step (entry (a, state)) := by
    unfold NestedTheta.Partial.observe graph
    rw [NestedTheta.Term.toTerm_toGraph]
    change (iter step (entry (a, state)) >>= fun output =>
      pure (point (output.get .head) (output.get (.tail .head)))) = _
    have forward (output : Point (σ := σ) (Carrier A E D)) :
        point (output.get .head) (output.get (.tail .head)) = output := by
      cases output with
      | cons a tail =>
        cases tail with
        | cons token tail => cases tail; rfl
    simp only [forward, bind_pure]
  rw [normalized, Silmaril.Elgot.StateT.run_iter]
  rw [OrderedTheta.iter_boundary _ step entry complete (step_denote s) (a, state)]
  exact Part.bind_some_eq_map _ _

private theorem map_eq_some_iff {X Y : Type u} (encode : X → Y) (injective : Function.Injective encode)
    (p : Part X) (x : X) : Part.map encode p = Part.some (encode x) ↔ p = Part.some x := by
  rw [Part.eq_some_iff, Part.eq_some_iff, Part.mem_map_iff]
  exact ⟨fun ⟨y, h, eq⟩ => injective eq ▸ h, fun h => ⟨x, h, rfl⟩⟩

private theorem complete_injective :
    Function.Injective (complete (A := A) (E := E) (D := D) (σ := σ)) := by
  rintro ⟨a, state⟩ ⟨b, token⟩ h
  have payload := congrArg (fun x : Point (σ := σ) (Carrier A E D) => x.get .head) h
  have tokenEq : state = token := congrArg
    (fun x : Point (σ := σ) (Carrier A E D) => x.get (.tail .head)) h
  have same := (TypeModel.coprodEquiv E D).symm.injective
    (Sum.inl.inj ((TypeModel.coprodEquiv (ExitCode E D) A).symm.injective payload))
  have restore (label : LabelDen [E,D]) : exitLabel (exitPayload label) = label := by
    rcases label with c | d | impossible
    · rfl
    · rfl
    · exact nomatch impossible
  exact Prod.ext ((restore a).symm.trans ((congrArg exitLabel same).trans (restore b))) tokenEq

theorem graph_returns_iff (s : Blocks Φ A B X Y K E D) (a : TyDen A)
    (label : LabelDen [E,D]) (initial final : σ) :
    (iter (round (ε := ε) (m := StateT σ Part.{u}) s) a).run initial = Part.some (label, final) ↔
      returns (ε := ε) (graph s) a initial label final := by
  rw [returns, ← NestedTheta.Partial.observe_eq_some, wire_iterates]
  exact (map_eq_some_iff _ complete_injective _ (label, final)).symm

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Proofs
