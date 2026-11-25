module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Proofs

open TwoBlock.ExplicitRuntime (PrimitiveAgreement)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (Env LabelDen)
open OrderedTheta (carried results pack packChoice point)
open OrderedRuntime.Structured (Values RuntimeValues Threaded Model)
open Silmaril.Elgot (iter)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateM σ)]
variable {A B C D : τ}

set_option backward.isDefEq.respectTransparency false

private def completeBody (out : TyDen D ⊕ TyDen A) : (TyDen C ⊕ TyDen D) ⊕ TyDen A :=
  Sum.map Sum.inr id out

private theorem round_total (s : Blocks Φ A B C D) (a : TyDen A) (state : σ) :
    (round (ε := ε) (m := StateM σ) s a).run state =
      let header := (callCase (ε := ε) (m := StateM σ) s.header a).run state
      match header.1 with
      | .inl c => (.inl (.inl c), header.2)
      | .inr b => Prod.map completeBody id ((callCase (ε := ε) (m := StateM σ) s.body b).run header.2) := by
  rw [round, StateT.run_bind]
  obtain ⟨result, token⟩ := (callCase (ε := ε) (m := StateM σ) s.header a).run state
  cases result with
  | inl c => rfl
  | inr b =>
    change ((callCase (ε := ε) (m := StateM σ) s.body b >>= fun
      | .inl d => pure (.inl (.inr d) : (TyDen C ⊕ TyDen D) ⊕ TyDen A)
      | .inr a => pure (.inr a)).run token) =
        Prod.map completeBody id ((callCase (ε := ε) (m := StateM σ) s.body b).run token)
    rw [StateT.run_bind]
    obtain ⟨result, token⟩ := (callCase (ε := ε) (m := StateM σ) s.body b).run token
    cases result <;> rfl

section

variable [InstructionModel Φ τ ε (StateT σ Part.{u})]

private theorem callCase_run (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    {X Y Z : τ} (op : TwoBlock.Instruction Φ X (Silmaril.coprod Y Z)) (x : TyDen X) (state : σ) :
    (callCase (ε := ε) (m := StateT σ Part.{u}) op x).run state =
      Part.some ((callCase (ε := ε) (m := StateM σ) op x).run state) := by
  simp only [callCase, StateT.run_bind, StateT.run_pure, agrees.call_run, Part.bind_eq_bind, Part.bind_some]
  rfl

private theorem round_run (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (s : Blocks Φ A B C D) (a : TyDen A) (state : σ) :
    (round (ε := ε) (m := StateT σ Part.{u}) s a).run state =
      Part.some ((round (ε := ε) (m := StateM σ) s a).run state) := by
  rw [round_total]
  simp only [round, StateT.run_bind, callCase_run agrees, Part.bind_eq_bind, Part.bind_some]
  obtain ⟨result, next⟩ := (callCase (ε := ε) (m := StateM σ) s.header a).run state
  cases result with
  | inl c => rfl
  | inr b =>
    simp only [StateT.run_bind, callCase_run agrees, Part.bind_eq_bind, Part.bind_some]
    obtain ⟨result, next⟩ := (callCase (ε := ε) (m := StateM σ) s.body b).run next
    cases result <;> rfl

end

private abbrev WireValues := RuntimeValues (TyDen (τ := τ)) σ

private def armInput (saved : TyDen (Carrier A C D)) (route : TyDen (Route B C D)) (state : σ) :
    Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (armPorts A B C D)) :=
  .cons saved (.cons route (.cons state .nil))

private def resultPorts (output : Tuple (WireValues (τ := τ) (σ := σ))
    (Threaded (results (Carrier A C D)))) : Tuple (WireValues (τ := τ) (σ := σ))
      (Threaded (results (Carrier A C D))) :=
  .cons (output.get .head) (.cons (output.get (.tail .head)) (.cons (output.get (.tail (.tail .head))) .nil))

private theorem resultPorts_eq (output : Tuple (WireValues (τ := τ) (σ := σ))
    (Threaded (results (Carrier A C D)))) : resultPorts output = output := by
  cases output with
  | cons tag tail =>
    cases tail with
    | cons data tail =>
      cases tail with
      | cons token tail => cases tail; rfl

@[simp] private theorem fin_cases_one {F : Fin 2 → Sort*} (z : F 0) (s : (j : Fin 1) → F j.succ) :
    Fin.cases (motive := F) z s (1 : Fin 2) = s 0 :=
  Fin.cases_succ (motive := F) (0 : Fin 1)

private def tagged (result : ((TyDen C ⊕ TyDen D) ⊕ TyDen A) × σ) :=
  TwoBlock.ExplicitRuntime.Skeleton.tagged (enter (A := A) (C := C) (D := D)) (finish (A := A)) result

private theorem arm_exit (s : Blocks Φ A B C D) (fuel : Nat) (saved : TyDen (Carrier A C D))
    (c : TyDen C) (state : σ) :
    (Wiring.arms s 0).1.run (wireModel (ε := ε) (σ := σ)).toRVSDG fuel
      (armInput (B := B) saved ((TypeModel.coprodEquiv (ExitCode C D) B).symm
        (.inl ((TypeModel.coprodEquiv C D).symm (.inl c)))) state) =
      some (tagged (A := A) (D := D) (.inl (.inl c), state)) := by
  change some (resultPorts (A := A) (C := C) (D := D) (OrderedRuntime.Structured.decode
    (value := TyDen (τ := τ)) (ρ := σ) (ts := results (Carrier A C D))
    ((match TypeModel.coprodEquiv (ExitCode C D) B ((TypeModel.coprodEquiv (ExitCode C D) B).symm
        (.inl ((TypeModel.coprodEquiv C D).symm (.inl c)))) with
      | .inl out => packChoice (.inl ((TypeModel.coprodEquiv (ExitCode C D) A).symm (.inl out)))
      | .inr _ => packChoice (.inr saved)), state))) = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem arm_body (s : Blocks Φ A B C D) (fuel : Nat) (saved : TyDen (Carrier A C D))
    (b : TyDen B) (state : σ) :
    (Wiring.arms s 1).1.run (wireModel (ε := ε) (σ := σ)).toRVSDG fuel
      (armInput (B := B) saved ((TypeModel.coprodEquiv (ExitCode C D) B).symm (.inr b)) state) =
      some (tagged (C := C) (Prod.map completeBody id
        ((callCase (ε := ε) (m := StateM σ) s.body b).run state))) := by
  simp only [Wiring.arms, fin_cases_one]
  change some (resultPorts (A := A) (C := C) (D := D) (OrderedRuntime.Structured.decode
    (value := TyDen (τ := τ)) (ρ := σ) (ts := results (Carrier A C D)) (((match
    TypeModel.coprodEquiv (ExitCode C D) B ((TypeModel.coprodEquiv (ExitCode C D) B).symm (.inr b)) with
    | .inl out => pure (packChoice (.inl ((TypeModel.coprodEquiv (ExitCode C D) A).symm (.inl out))))
    | .inr payload => callCase (ε := ε) s.body payload >>= fun result => pure (packChoice (Sum.map
        (fun d => finish (A := A) (C := C) (.inr d)) (enter (C := C) (D := D)) result))) :
      StateM σ _).run state))) = _
  rw [Equiv.apply_symm_apply]
  change some (resultPorts (A := A) (C := C) (D := D) (OrderedRuntime.Structured.decode
    (value := TyDen (τ := τ)) (ρ := σ) (ts := results (Carrier A C D))
    ((callCase (ε := ε) (m := StateM σ) s.body b >>= fun result => pure (packChoice (Sum.map
      (fun d => finish (A := A) (C := C) (.inr d)) (enter (C := C) (D := D)) result))).run state))) = _
  rw [StateT.run_bind]
  obtain ⟨result, token⟩ := (callCase (ε := ε) (m := StateM σ) s.body b).run state
  cases result <;> rfl

private def route (out : TyDen C ⊕ TyDen B) : TyDen (ExitCode C D) ⊕ TyDen B :=
  Sum.map (fun c => (TypeModel.coprodEquiv C D).symm (.inl c)) id out

private theorem header_run (s : Blocks Φ A B C D) (a : TyDen A) (state : σ) :
    ((wireModel (ε := ε) (σ := σ)).step (Wiring.header s) (pack (enter a))).run state =
      Prod.map (fun out => routeResult (route (D := D) out)) id
        ((callCase (ε := ε) (m := StateM σ) s.header a).run state) := by
  change ((match TypeModel.coprodEquiv (ExitCode C D) A (enter a) with
    | .inl out => pure (routeResult (.inl out))
    | .inr a => callCase (ε := ε) s.header a >>= fun result => pure (routeResult (route result))) :
      StateM σ _).run state = _
  rw [enter, Equiv.apply_symm_apply]
  rfl

private theorem body_run (s : Blocks Φ A B C D) (fuel : Nat) (a : TyDen A) (state : σ) :
    (TwoBlock.ExplicitRuntime.Skeleton.thetaBody (Wiring.header s) (Wiring.arms s)).1.run (wireModel (ε := ε) (σ := σ)).toRVSDG fuel
      (point (enter (C := C) (D := D) a) state) =
      some (tagged ((round (ε := ε) (m := StateM σ) s a).run state)) := by
  change (let output := OrderedRuntime.Structured.decode
            (value := TyDen (τ := τ)) (ρ := σ) (ts := headerPorts B C D)
            (((wireModel (ε := ε) (σ := σ)).step (Wiring.header s) (pack (enter a))).run state)
          let tag := (output.get .head).down
          (Wiring.arms s tag).1.run (wireModel (ε := ε) (σ := σ)).toRVSDG fuel
            (armInput (enter a) (output.get (.tail .head)) (output.get (.tail (.tail .head)))) >>= fun output =>
            some (resultPorts output)) = _
  rw [header_run, round_total]
  obtain ⟨result, token⟩ := (callCase (ε := ε) (m := StateM σ) s.header a).run state
  cases result with
  | inl c =>
    change (Wiring.arms s 0).1.run (wireModel (ε := ε) (σ := σ)).toRVSDG fuel
      (armInput (enter a) ((TypeModel.coprodEquiv (ExitCode C D) B).symm
        (.inl ((TypeModel.coprodEquiv C D).symm (.inl c)))) token) >>= _ = _
    rw [arm_exit]
    rfl
  | inr b =>
    change (Wiring.arms s 1).1.run (wireModel (ε := ε) (σ := σ)).toRVSDG fuel
      (armInput (enter a) ((TypeModel.coprodEquiv (ExitCode C D) B).symm (.inr b)) token) >>= _ = _
    rw [arm_body]
    change some (resultPorts _) = some _
    rw [resultPorts_eq]

private theorem map_eq_some_iff {X Y : Type u} (encode : X → Y) (injective : Function.Injective encode)
    (p : Part X) (x : X) : Part.map encode p = Part.some (encode x) ↔ p = Part.some x := by
  rw [Part.eq_some_iff, Part.eq_some_iff, Part.mem_map_iff]
  exact ⟨fun ⟨y, h, eq⟩ => injective eq ▸ h, fun h => ⟨x, h, rfl⟩⟩

private theorem finish_injective :
    Function.Injective (finish (A := A) (C := C) (D := D)) := by
  intro x y h
  exact (TypeModel.coprodEquiv C D).symm.injective
    (Sum.inl.inj ((TypeModel.coprodEquiv (ExitCode C D) A).symm.injective h))

private theorem exit_injective : Function.Injective (exitLabel (C := C) (D := D)) := by
  rintro (c | d) (c' | d') h <;> cases h <;> rfl

variable [InstructionModel Φ τ ε (StateT σ Part.{u})]

private theorem erasedCarrier_iter (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (s : Blocks Φ A B C D) (a : TyDen A) (state : σ) :
    erasedCarrier (ε := ε) s a state =
      Part.map (fun out => (finish (A := A) out.1, out.2))
        ((iter (round (ε := ε) (m := StateT σ Part.{u}) s) a).run state) :=
  TwoBlock.ExplicitRuntime.Skeleton.observeCarrier_iter (Wiring.header s) (Wiring.arms s)
    (wireModel (ε := ε)) enter finish (round (ε := ε) s)
    (fun input => (round (ε := ε) (m := StateM σ) s input.1).run input.2)
    (fun input => round_run agrees s input.1 input.2)
    (fun fuel input => body_run s fuel input.1 input.2) (a, state)

theorem erasedCarrier_eq (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A C D}
    (rel : Related A B C D r g) (a : TyDen A) (state : σ) :
    erasedCarrier (ε := ε) rel.instructions a state = (denoteCarrier (ε := ε) (m := StateT σ Part.{u}) g a).run state := by
  rw [erasedCarrier_iter agrees, rel.denoteCarrier_eq, StateT.run_bind]
  exact (Part.bind_some_eq_map _ _).symm

private theorem erasedObservation_iter (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (s : Blocks Φ A B C D) (a : TyDen A) (state : σ) :
    erasedObservation (ε := ε) s a state =
      Part.map (fun out => (exitLabel out.1, out.2))
        ((iter (round (ε := ε) (m := StateT σ Part.{u}) s) a).run state) := by
  rw [erasedObservation, erasedCarrier_iter agrees, Part.bind_map]
  rw [← Part.bind_some_eq_map]
  congr 1
  funext p
  obtain ⟨out, token⟩ := p
  simp only [decode, finish, Equiv.apply_symm_apply]
  rfl

theorem erased_denote (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A C D}
    (rel : Related A B C D r g) (env : Env [A]) (state : σ) :
    erasedObservation (ε := ε) rel.instructions env.2 state = (denote (ε := ε) (m := StateT σ Part.{u}) g env).run state := by
  rw [denote, StateT.run_bind, ← erasedCarrier_eq agrees rel, erasedObservation]
  rfl

theorem erased_returns_iff (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (s : Blocks Φ A B C D) (a : TyDen A) (out : TyDen C ⊕ TyDen D) (initial final : σ) :
    erasedObservation (ε := ε) s a initial = Part.some (exitLabel out, final) ↔
      (graph s).Returns (wireModel (ε := ε)).toRVSDG (point (enter a) initial) (point (finish out) final) := by
  have observes : erasedCarrier (ε := ε) s a initial = Part.some (finish out, final) ↔
      (graph s).Returns (wireModel (ε := ε)).toRVSDG (point (enter a) initial) (point (finish out) final) :=
    TwoBlock.ExplicitRuntime.Skeleton.observeCarrier_iff (Wiring.header s) (Wiring.arms s)
      (wireModel (ε := ε)) (enter a) (finish out) initial final
  rw [← observes, erasedObservation_iter agrees, erasedCarrier_iter agrees]
  exact (map_eq_some_iff _ (exit_injective.prodMap Function.injective_id) _ (out, final)).trans
    (map_eq_some_iff _ (finish_injective.prodMap Function.injective_id) _ (out, final)).symm

theorem exitLabel_payload (label : LabelDen [C, D]) : exitLabel (exitPayload label) = label := by
  rcases label with c | d | impossible
  · rfl
  · rfl
  · exact nomatch impossible

theorem region_returns_iff (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
      (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A C D}
    (rel : Related A B C D r g) (env : Env [A]) (label : LabelDen [C, D]) (initial final : σ) :
    (Isotope.LambdaSSA.Semantics.Monadic.Region.denote (ε := ε) (m := StateT σ Part.{u})
      rel.typing env).run initial = Part.some (label, final) ↔
      (graph rel.instructions).Returns (wireModel (ε := ε)).toRVSDG (point (enter env.2) initial)
        (point (finish (exitPayload label)) final) := by
  rw [rel.chosenDenote_eq coherent, ← erased_denote agrees rel]
  have observes := erased_returns_iff agrees rel.instructions env.2 (exitPayload label) initial final
  rw [exitLabel_payload] at observes
  exact observes

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Proofs
