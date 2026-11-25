module

public import Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open OrderedTheta (carried results pack packChoice point)
open OrderedRuntime.Structured (Values RuntimeValues Threaded Model)
open Silmaril.Elgot (iter)
open NestedTheta (stepWith)
open TwoBlock.TwoExit (Carrier Route ExitCode Pure headerPorts armPorts routeResult callCase enter finish exitLabel)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B X C D : τ}

set_option backward.isDefEq.respectTransparency false

private abbrev WireValues := RuntimeValues (TyDen (τ := τ)) σ
private abbrev Result (K : τ) := Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (results K))

private def armInput (saved : TyDen (Carrier A C D)) (route : TyDen (Route B C D)) (state : σ) :
    Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (armPorts A B C D)) :=
  .cons saved (.cons route (.cons state .nil))

private def rewire {K : τ} (output : Result (σ := σ) K) : Result (σ := σ) K :=
  .cons (output.get .head) (.cons (output.get (.tail .head)) (.cons (output.get (.tail (.tail .head))) .nil))

private theorem rewire_eq (output : Result (σ := σ) (Carrier A C D)) : rewire output = output := by
  cases output with
  | cons tag tail =>
    cases tail with
    | cons value tail =>
      cases tail with
      | cons token tail => cases tail; rfl

private def route (result : TyDen C ⊕ TyDen B) : TyDen (ExitCode C D) ⊕ TyDen B :=
  Sum.map (fun c => (TypeModel.coprodEquiv C D).symm (.inl c)) id result

private def headerTuple (result : (TyDen C ⊕ TyDen B) × σ) :
    Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (headerPorts B C D)) :=
  OrderedRuntime.Structured.decode (routeResult (route result.1), result.2)

private def tagged (result : ((TyDen C ⊕ TyDen D) ⊕ TyDen A) × σ) :=
  TwoBlock.ExplicitRuntime.Skeleton.tagged (enter (A := A) (C := C) (D := D)) (finish (A := A)) result

@[simp] private theorem fin_cases_one {F : Fin 2 → Sort*} (z : F 0) (s : (j : Fin 1) → F j.succ) :
    Fin.cases (motive := F) z s (1 : Fin 2) = s 0 :=
  Fin.cases_succ (motive := F) (0 : Fin 1)

private theorem header_denote (s : Blocks Φ A B X C D) (a : TyDen A) (state : σ) :
    (wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (OrderedTheta.carriedData _) (TwoBlock.ExplicitRuntime.Skeleton.headerData _) (.effect (.header s.header)))
      (point (enter a) state) =
      Part.map (headerTuple (D := D)) ((callCase (ε := ε) (m := StateT σ Part.{u}) s.header a).run state) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := headerPorts B C D))
    (((match TypeModel.coprodEquiv (ExitCode C D) A (enter a) with
    | .inl out => pure (routeResult (.inl out))
    | .inr a => callCase (ε := ε) (m := StateT σ Part.{u}) s.header a >>= fun result => pure (routeResult (route result))) :
      StateT σ Part.{u} _).run state) = _
  rw [enter, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some_eq_map]
  rw [Part.map_map]
  rfl

private theorem arm_denote (op : OrderedRuntime.Structured.Instruction (Pure τ) (Effect Φ) (armPorts A B C D) (results (Carrier A C D)))
    (saved : TyDen (Carrier A C D)) (route : TyDen (Route B C D)) (state : σ) :
    (TwoBlock.ExplicitRuntime.Skeleton.arm op).1.denoteOpenWith
      (wireModel (ε := ε) (σ := σ)) (armInput (B := B) saved route state) PUnit.unit =
        Part.map (OrderedRuntime.Structured.decode (ts := results (Carrier A C D)))
          (((orderedModel (ε := ε) (m := StateT σ Part.{u})).step op
            (.cons saved (.cons route .nil))).run state) := by
  change (Part.map _ _ >>= fun output => pure (rewire output)) = _
  simp only [rewire_eq, bind_pure]
  rfl

private theorem arm_exit (s : Blocks Φ A B X C D) (saved : TyDen (Carrier A C D))
    (c : TyDen C) (state : σ) :
    (Wiring.arms s 0).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
      (armInput (B := B) saved ((TypeModel.coprodEquiv (ExitCode C D) B).symm
        (.inl ((TypeModel.coprodEquiv C D).symm (.inl c)))) state) PUnit.unit =
      Part.some (tagged (A := A) (D := D) (.inl (.inl c), state)) := by
  change (TwoBlock.ExplicitRuntime.Skeleton.arm (.pure (Pure.exit (A := A) (B := B) (C := C) (D := D)))).1.denoteOpenWith
    (wireModel (Φ := Φ) (ε := ε) (σ := σ)) _ PUnit.unit = _
  rw [arm_denote]
  change Part.map (OrderedRuntime.Structured.decode (ts := results (Carrier A C D))) (Part.some
    ((match TypeModel.coprodEquiv (ExitCode C D) B ((TypeModel.coprodEquiv (ExitCode C D) B).symm
        (.inl ((TypeModel.coprodEquiv C D).symm (.inl c)))) with
      | .inl out => packChoice (.inl ((TypeModel.coprodEquiv (ExitCode C D) A).symm (.inl out)))
      | .inr _ => packChoice (.inr saved)), state)) = _
  rw [Equiv.apply_symm_apply]
  rfl

private def completeBody (out : TyDen D ⊕ TyDen A) : (TyDen C ⊕ TyDen D) ⊕ TyDen A :=
  Sum.map Sum.inr id out

private theorem first_denote (s : Blocks Φ A B X C D) (saved : TyDen (Carrier A C D))
    (b : TyDen B) (state : σ) :
    (wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (.value (.value .nil)) (.value .nil) (.effect (.first s.first)))
      (armInput saved (bodyRoute b) state) =
      Part.map (fun p => point (bodyRoute (C := C) (D := D) p.1) p.2)
        ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) s.first b).run state) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := carried (Route X C D)))
    (((match TypeModel.coprodEquiv (ExitCode C D) B (bodyRoute b) with
      | .inl out => pure (pack ((TypeModel.coprodEquiv (ExitCode C D) X).symm (.inl out)))
      | .inr b => TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) s.first b >>= fun x =>
          pure (pack (bodyRoute x))) : StateT σ Part.{u} _).run state) = _
  rw [bodyRoute, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

private theorem last_denote (s : Blocks Φ A B X C D) (x : TyDen X) (state : σ) :
    (wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (.value .nil) (OrderedTheta.resultData _) (.effect (.last s.last)))
      (point (bodyRoute x) state) =
      Part.map (fun p => tagged (C := C) (Prod.map completeBody id p))
        ((callCase (ε := ε) (m := StateT σ Part.{u}) s.last x).run state) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := results (Carrier A C D)))
    (((match TypeModel.coprodEquiv (ExitCode C D) X (bodyRoute x) with
      | .inl out => pure (exitResult out)
      | .inr x => callCase (ε := ε) (m := StateT σ Part.{u}) s.last x >>= fun r => pure (lastResult r)) :
      StateT σ Part.{u} _).run state) = _
  rw [bodyRoute, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  congr 1
  funext p
  rcases p with ⟨(d | a), token⟩ <;> rfl

private theorem arm_body (s : Blocks Φ A B X C D) (saved : TyDen (Carrier A C D))
    (b : TyDen B) (state : σ) :
    (Wiring.arms s 1).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
      (armInput saved (bodyRoute b) state) PUnit.unit =
      ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) s.first b).run state).bind fun p =>
        Part.map (fun out => tagged (C := C) (Prod.map completeBody id out))
          ((callCase (ε := ε) (m := StateT σ Part.{u}) s.last p.1).run p.2) := by
  simp only [Wiring.arms, fin_cases_one]
  change ((wireModel (ε := ε) (σ := σ)).primitive
       (.ordered (.value (.value .nil)) (.value .nil) (.effect (.first s.first)))
       (armInput saved (bodyRoute b) state) >>= fun mid =>
    (wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (.value .nil) (OrderedTheta.resultData _) (.effect (.last s.last)))
      (point (mid.get .head) (mid.get (.tail .head))) >>= fun output => pure (rewire output)) = _
  simp only [rewire_eq, first_denote, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some_right, Part.bind_map]
  congr 1
  funext p
  exact last_denote s p.1 p.2

private theorem body_denote (s : Blocks Φ A B X C D) (a : TyDen A) (state : σ) :
    (Wiring.thetaBody s).1.denoteOpenWith
      (wireModel (ε := ε) (σ := σ)) (point (enter a) state) PUnit.unit =
      Part.map tagged ((round (ε := ε) (m := StateT σ Part.{u}) s a).run state) := by
  change ((wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (OrderedTheta.carriedData _) (TwoBlock.ExplicitRuntime.Skeleton.headerData _) (.effect (.header s.header)))
      (point (enter a) state) >>= fun output =>
    (Wiring.arms s (output.get .head).down).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
      (armInput (enter a) (output.get (.tail .head)) (output.get (.tail (.tail .head)))) PUnit.unit >>=
    fun result => pure (rewire result)) = _
  simp only [rewire_eq, header_denote, round, StateT.run_bind, Part.bind_eq_bind,
    Part.pure_eq_some, Part.bind_some_right, Part.bind_map, Part.map_bind]
  congr 1
  funext p
  obtain ⟨result, token⟩ := p
  cases result with
  | inl c =>
    change (Wiring.arms s 0).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
      (armInput (enter a) ((TypeModel.coprodEquiv (ExitCode C D) B).symm
        (.inl ((TypeModel.coprodEquiv C D).symm (.inl c)))) token) PUnit.unit = _
    rw [arm_exit]
    rfl
  | inr b =>
    change (Wiring.arms s 1).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
      (armInput (enter a) (bodyRoute b) token) PUnit.unit = _
    rw [arm_body]
    simp only [StateT.run_bind, Part.bind_eq_bind, StateT.run_pure, Part.pure_eq_some,
      Part.map_bind, Part.bind_some_eq_map, Part.map_map]
    rfl

private abbrev CarrierTuple (K : τ) :=
  Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (carried K))

private def entry (p : TyDen A × σ) : CarrierTuple (σ := σ) (Carrier A C D) :=
  point (enter p.1) p.2

private def complete (p : (TyDen C ⊕ TyDen D) × σ) : CarrierTuple (σ := σ) (Carrier A C D) :=
  point (finish p.1) p.2

private noncomputable def wireBody (s : Blocks Φ A B X C D) (input : CarrierTuple (σ := σ) (Carrier A C D)) :=
  (Wiring.thetaBody s).1.denoteOpenWith
    (wireModel (ε := ε) (σ := σ)) input PUnit.unit

private theorem step_denote (s : Blocks Φ A B X C D) (input : TyDen A × σ) :
    stepWith (wireBody (ε := ε) s) (entry input) =
      Silmaril.Elgot.StateT.body (round (ε := ε) (m := StateT σ Part.{u}) s) input >>= fun result =>
        pure (Sum.map complete entry result) := by
  change stepWith (wireBody (ε := ε) s) (point (enter input.1) input.2) = _
  unfold stepWith
  rw [Bind.kleisliRight]
  change (wireBody (ε := ε) s (point (enter input.1) input.2) >>= _) = _
  unfold wireBody
  rw [body_denote]
  simp only [Silmaril.Elgot.StateT.body, Part.bind_eq_bind, Part.bind_map, Part.bind_assoc]
  congr 1
  funext p
  rcases p with ⟨(out | next), state⟩ <;>
    simp only [Function.comp_apply, Part.pure_eq_some, Part.bind_some] <;> rfl

private theorem wire_iterates (s : Blocks Φ A B X C D) (a : TyDen A) (state : σ) :
    NestedTheta.Partial.observe (wireModel (ε := ε) (σ := σ)) (graph s) (point (enter a) state) =
      Part.map (complete (A := A)) ((iter (round (ε := ε) (m := StateT σ Part.{u}) s) a).run state) := by
  let step := stepWith (wireBody (ε := ε) (σ := σ) s)
  have normalized :
      NestedTheta.Partial.observe (wireModel (ε := ε) (σ := σ)) (graph s) (point (enter a) state) =
        iter step (entry (a, state)) := by
    unfold NestedTheta.Partial.observe graph
    rw [NestedTheta.Term.toTerm_toGraph]
    change (iter step (entry (a, state)) >>= fun output =>
      pure (point (output.get .head) (output.get (.tail .head)))) = _
    have forward (output : CarrierTuple (σ := σ) (Carrier A C D)) :
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
    Function.Injective (complete (A := A) (C := C) (D := D) (σ := σ)) := by
  rintro ⟨a, state⟩ ⟨b, token⟩ h
  have payload := congrArg (fun x : CarrierTuple (σ := σ) (Carrier A C D) => x.get .head) h
  have tokenEq : state = token := congrArg
    (fun x : CarrierTuple (σ := σ) (Carrier A C D) => x.get (.tail .head)) h
  have ha : a = b := (TypeModel.coprodEquiv C D).symm.injective
    (Sum.inl.inj ((TypeModel.coprodEquiv (ExitCode C D) A).symm.injective payload))
  exact Prod.ext ha tokenEq

private theorem exit_injective : Function.Injective (exitLabel (C := C) (D := D)) := by
  rintro (c | d) (c' | d') h <;> cases h <;> rfl

private theorem exitLabel_payload (label : LabelDen [C, D]) : exitLabel (exitPayload label) = label := by
  rcases label with c | d | impossible
  · rfl
  · rfl
  · exact nomatch impossible

theorem graph_returns_iff (s : Blocks Φ A B X C D) (env : Env [A])
    (label : LabelDen [C, D]) (initial final : σ) :
    (regionAction (ε := ε) (m := StateT σ Part.{u}) s env).run initial = Part.some (label, final) ↔
      returns (ε := ε) (graph s) env.2 initial label final := by
  rw [regionAction, StateT.run_bind, returns, ← NestedTheta.Partial.observe_eq_some, wire_iterates]
  let p := (iter (round (ε := ε) (m := StateT σ Part.{u}) s) env.2).run initial
  change p.bind (fun out => Part.some (exitLabel out.1, out.2)) = Part.some (label, final) ↔
    Part.map (complete (A := A)) p = Part.some (complete (exitPayload label, final))
  rw [Part.bind_some_eq_map]
  conv_lhs => rhs; rw [← exitLabel_payload label]
  exact (map_eq_some_iff _ (exit_injective.prodMap Function.injective_id) p (exitPayload label, final)).trans
    (map_eq_some_iff _ complete_injective p (exitPayload label, final)).symm

end Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Proofs
