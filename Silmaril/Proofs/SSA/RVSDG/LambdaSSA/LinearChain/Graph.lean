module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open OrderedTheta (carried results pack packChoice point)
open OrderedRuntime.Structured
open Silmaril.Elgot (iter)
open NestedTheta (stepWith)
open TwoBlock.TwoExit (Carrier Route ExitCode Pure headerPorts armPorts routeResult callCase enter finish exitLabel)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B X C D : τ} {tail : List τ}

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

private def tagged (result : (LabelDen [C,D] ⊕ TyDen A) × σ) :
    Result (σ := σ) (Carrier A C D) :=
  TwoBlock.ExplicitRuntime.Skeleton.tagged (enter (A := A) (C := C) (D := D))
    (fun label => finish (A := A) (exitPayload label)) result

@[simp] private theorem fin_cases_one {F : Fin 2 → Sort*} (z : F 0) (s : (j : Fin 1) → F j.succ) :
    Fin.cases (motive := F) z s (1 : Fin 2) = s 0 :=
  Fin.cases_succ (motive := F) (0 : Fin 1)

private theorem header_denote (s : Blocks Φ A B C D tail) (a : TyDen A) (state : σ) :
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

private theorem arm_exit (s : Blocks Φ A B C D tail) (saved : TyDen (Carrier A C D))
    (c : TyDen C) (state : σ) :
    (Wiring.arms s.body 0).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
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

private def bodyResult (r : (TyDen D ⊕ TyDen A) × σ) : Result (σ := σ) (Carrier A C D) :=
  OrderedRuntime.Structured.decode (lastResult r.1, r.2)

private theorem forward_denote (op : TwoBlock.Instruction Φ B X) (b : TyDen B) (state : σ) :
    (wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (.value .nil) (.value .nil) (.effect (.forward (C := C) (D := D) op)))
      (point (bodyRoute b) state) =
      Part.map (fun p => point (bodyRoute (C := C) (D := D) p.1) p.2)
        ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) op b).run state) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := carried (Route X C D)))
    (((match TypeModel.coprodEquiv (ExitCode C D) B (bodyRoute b) with
      | .inl out => pure (pack ((TypeModel.coprodEquiv (ExitCode C D) X).symm (.inl out)))
      | .inr b => TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) op b >>= fun x =>
          pure (pack (bodyRoute x))) : StateT σ Part.{u} _).run state) = _
  rw [bodyRoute, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

private theorem last_denote (op : TwoBlock.Instruction Φ B (Silmaril.coprod D A)) (b : TyDen B) (state : σ) :
    (wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (.value .nil) (OrderedTheta.resultData _) (.effect (Effect.last (C := C) op)))
      (point (bodyRoute b) state) =
      Part.map (bodyResult (C := C)) ((callCase (ε := ε) (m := StateT σ Part.{u}) op b).run state) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := results (Carrier A C D)))
    (((match TypeModel.coprodEquiv (ExitCode C D) B (bodyRoute b) with
      | .inl out => pure (exitResult out)
      | .inr b => callCase (ε := ε) (m := StateT σ Part.{u}) op b >>= fun r => pure (lastResult r)) :
      StateT σ Part.{u} _).run state) = _
  rw [bodyRoute, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

omit [TypeFormers τ] [Isotope.Subtyping τ] [TypeModel τ] in
private theorem read_newest {F : OrderedRuntime.Structured.Ty τ → Type u}
    {args out : Ports (OrderedRuntime.Structured.Ty τ)} {t : OrderedRuntime.Structured.Ty τ}
    (p : Port out t) (past : List (Ports (OrderedRuntime.Structured.Ty τ))) (entry : Tuple F args)
    (locals : Locals F past) (outcome : Tuple F out) :
    readOrigin (Wiring.newest p past) entry (locals.snoc outcome) = outcome.get p := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

private theorem terminal_wires {args : Ports (OrderedRuntime.Structured.Ty τ)}
    (past : List (Ports (OrderedRuntime.Structured.Ty τ)))
    (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past)
    (output : Result (σ := σ) (Carrier A C D)) :
    Wires.read (withRuntime (nextRuntime past (results (Carrier A C D)))
      (.cons (Wiring.newest .head past) (.cons (Wiring.newest (.tail .head) past) .nil)))
      entry (locals.snoc output) = output := by
  have token : nextRuntime (args := Threaded args) past (results (Carrier A C D)) =
      Wiring.newest (runtimePort (results (Carrier A C D))) past := rfl
  rw [token, read_appended, read_cons, read_cons]
  simp only [read_newest]
  exact rewire_eq output

private theorem chain_denote {args : Ports (OrderedRuntime.Structured.Ty τ)} (entryData : Data args)
    (body : Body Φ A D B tail)
    (past : List (Ports (OrderedRuntime.Structured.Ty τ)))
    (live : Origin (Threaded args) past runtime) (source : Origin (Threaded args) past (.value (Route B C D)))
    (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past)
    (b : TyDen B) (active : readOrigin source entry locals = bodyRoute b) :
    (Wiring.chain entryData body past live source).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
      entry locals =
      Part.map (bodyResult (C := C)) (((body.fold (ε := ε) (m := StateT σ Part.{u})) b).run
        (readOrigin live entry locals)) := by
  induction body generalizing past with
  | last op =>
    simp only [Wiring.chain, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
      NestedTheta.Node.ofBase, primitiveNode, read_appended, read_cons]
    let wires : Wires (Threaded args) (past ++ [Wiring.result A C D]) (Wiring.result A C D) :=
      withRuntime (nextRuntime past (results (Carrier A C D)))
        (.cons (Wiring.newest .head past) (.cons (Wiring.newest (.tail .head) past) .nil))
    change ((wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (.value .nil) (OrderedTheta.resultData _) (.effect (Effect.last (C := C) op)))
      (point (readOrigin source entry locals) (readOrigin live entry locals)) >>= fun output =>
        pure (wires.read entry (locals.snoc output))) = _
    simp only [wires, terminal_wires, bind_pure, active, Body.fold]
    exact last_denote (ε := ε) (σ := σ) op b (readOrigin live entry locals)
  | @next B X xs op rest ih =>
    simp only [Wiring.chain, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
      NestedTheta.Node.ofBase, primitiveNode, read_appended, read_cons]
    let token := nextRuntime (args := Threaded args) past (carried (Route X C D))
    let value := Wiring.newest (args := Threaded args) (out := Wiring.intermediate X C D) .head past
    let child := Wiring.chain entryData rest (past ++ [Wiring.intermediate X C D]) token value
    change ((wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (.value .nil) (.value .nil) (.effect (.forward (C := C) (D := D) op)))
      (point (readOrigin source entry locals) (readOrigin live entry locals)) >>= fun output =>
        child.1.denoteOpenWith (wireModel (ε := ε) (σ := σ)) entry (locals.snoc output)) = _
    rw [active, forward_denote]
    simp only [Body.fold, StateT.run_bind, Part.bind_eq_bind, Part.bind_map, Part.map_bind]
    congr 1
    funext p
    have selected : readOrigin value entry (locals.snoc (point (bodyRoute p.1) p.2)) = bodyRoute p.1 := by
      change readOrigin (Wiring.newest (out := Wiring.intermediate X C D) .head past) entry
        (locals.snoc (point (bodyRoute p.1) p.2)) = bodyRoute p.1
      rw [read_newest]
      rfl
    have rt : readOrigin token entry (locals.snoc (point (bodyRoute p.1) p.2)) = p.2 := by
      change readOrigin (Wiring.newest (runtimePort (carried (Route X C D))) past) entry
        (locals.snoc (point (bodyRoute p.1) p.2)) = p.2
      rw [read_newest]
      rfl
    unfold child
    rw [ih _ _ _ _ _ selected, rt]

private theorem arm_body (s : Blocks Φ A B C D tail) (saved : TyDen (Carrier A C D))
    (b : TyDen B) (state : σ) :
    (Wiring.arms s.body 1).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
      (armInput saved (bodyRoute b) state) PUnit.unit =
      Part.map (bodyResult (C := C)) ((s.body.fold (ε := ε) (m := StateT σ Part.{u}) b).run state) := by
  simp only [Wiring.arms, fin_cases_one, Wiring.bodyArm]
  exact chain_denote _ s.body [] _ _ _ PUnit.unit b rfl

private theorem body_denote (s : Blocks Φ A B C D tail) (a : TyDen A) (state : σ) :
    (Wiring.thetaBody s).1.denoteOpenWith
      (wireModel (ε := ε) (σ := σ)) (point (enter a) state) PUnit.unit =
      Part.map tagged ((round (ε := ε) (m := StateT σ Part.{u}) s a).run state) := by
  change ((wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (OrderedTheta.carriedData _) (TwoBlock.ExplicitRuntime.Skeleton.headerData _) (.effect (.header s.header)))
      (point (enter a) state) >>= fun output =>
    (Wiring.arms s.body (output.get .head).down).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
      (armInput (enter a) (output.get (.tail .head)) (output.get (.tail (.tail .head)))) PUnit.unit >>=
    fun result => pure (rewire result)) = _
  simp only [rewire_eq, header_denote, round, StateT.run_bind, Part.bind_eq_bind,
    Part.pure_eq_some, Part.bind_some_right, Part.bind_map, Part.map_bind]
  congr 1
  funext p
  obtain ⟨result, token⟩ := p
  cases result with
  | inl c =>
    change (Wiring.arms s.body 0).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
      (armInput (enter a) ((TypeModel.coprodEquiv (ExitCode C D) B).symm
        (.inl ((TypeModel.coprodEquiv C D).symm (.inl c)))) token) PUnit.unit = _
    rw [arm_exit]
    rfl
  | inr b =>
    change (Wiring.arms s.body 1).1.denoteOpenWith (wireModel (ε := ε) (σ := σ))
      (armInput (enter a) (bodyRoute b) token) PUnit.unit = _
    rw [arm_body]
    simp only [StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
    rw [← Part.bind_some_eq_map]
    congr 1
    funext p
    rcases p with ⟨(d | a), token⟩ <;> rfl

private abbrev CarrierTuple (K : τ) :=
  Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (carried K))

private def entry (p : TyDen A × σ) : CarrierTuple (σ := σ) (Carrier A C D) :=
  point (enter p.1) p.2

private def complete (p : LabelDen [C,D] × σ) : CarrierTuple (σ := σ) (Carrier A C D) :=
  point (finish (exitPayload p.1)) p.2

private noncomputable def wireBody (s : Blocks Φ A B C D tail) (input : CarrierTuple (σ := σ) (Carrier A C D)) :=
  (Wiring.thetaBody s).1.denoteOpenWith
    (wireModel (ε := ε) (σ := σ)) input PUnit.unit

private theorem step_denote (s : Blocks Φ A B C D tail) (input : TyDen A × σ) :
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

private theorem wire_iterates (s : Blocks Φ A B C D tail) (a : TyDen A) (state : σ) :
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
  have same := (TypeModel.coprodEquiv C D).symm.injective
    (Sum.inl.inj ((TypeModel.coprodEquiv (ExitCode C D) A).symm.injective payload))
  have restore (label : LabelDen [C,D]) : exitLabel (exitPayload label) = label := by
    rcases label with c | d | impossible
    · rfl
    · rfl
    · exact nomatch impossible
  exact Prod.ext ((restore a).symm.trans ((congrArg exitLabel same).trans (restore b))) tokenEq

theorem graph_returns_iff (s : Blocks Φ A B C D tail) (env : Env [A])
    (label : LabelDen [C, D]) (initial final : σ) :
    (regionAction (ε := ε) (m := StateT σ Part.{u}) s env).run initial = Part.some (label, final) ↔
      returns (ε := ε) (graph s) env.2 initial label final := by
  rw [returns, ← NestedTheta.Partial.observe_eq_some, wire_iterates]
  exact (map_eq_some_iff _ complete_injective _ (label, final)).symm

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Proofs
