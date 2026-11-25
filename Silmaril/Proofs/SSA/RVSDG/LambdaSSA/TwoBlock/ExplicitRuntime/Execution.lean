module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Defs

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Proofs

open Silmaril.Elgot (iter)
open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (carried results point)
open OrderedRuntime.Structured

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateM σ)]
variable {A B C : τ}
set_option backward.isDefEq.respectTransparency false

section

variable [InstructionModel Φ τ ε (StateT σ Part.{u})]

private theorem call_run (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (op : TwoBlock.Instruction Φ A C) (a : TyDen A) (state : σ) :
    (call (ε := ε) (m := StateT σ Part.{u}) op a).run state =
      Part.some ((call (ε := ε) (m := StateM σ) op a).run state) := by
  simp only [call, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind]
  rw [agrees op.op (op.input.symm ▸ a) state, Part.bind_some]
  rfl

private theorem header_run (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (op : TwoBlock.Instruction Φ A (Silmaril.coprod A B)) (a : TyDen A) (state : σ) :
    (headerAction (ε := ε) (m := StateT σ Part.{u}) op a).run state =
      Part.some ((headerAction (ε := ε) (m := StateM σ) op a).run state) := by
  simp only [headerAction, StateT.run_bind, StateT.run_pure, call_run agrees,
    Part.bind_eq_bind, Part.bind_some]
  rfl

private theorem round_run (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (s : Blocks Φ A B) (a : TyDen A) (state : σ) :
    (round (ε := ε) (m := StateT σ Part.{u}) s a).run state =
      Part.some ((round (ε := ε) (m := StateM σ) s a).run state) := by
  simp only [round, StateT.run_bind, header_run agrees, Part.bind_eq_bind, Part.bind_some]
  obtain ⟨result, next⟩ := (headerAction (ε := ε) (m := StateM σ) s.header a).run state
  cases result with
  | inl a => rfl
  | inr b =>
    simp only [StateT.run_bind, StateT.run_pure, call_run agrees, Part.bind_eq_bind, Part.bind_some]
    rfl

end

private abbrev runtimeModel : RVSDG.Model (WireOp (τ := τ) Φ) :=
  (wireModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).toRVSDG

private def bodyResult (p : (TyDen A ⊕ TyDen A) × σ) :
    Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (results A)) :=
  match p.1 with
  | .inl a => .cons ⟨0⟩ (point a p.2)
  | .inr a => .cons ⟨1⟩ (point a p.2)

private def armInput (saved : TyDen A) (sum : TyDen (Silmaril.coprod A B)) (state : σ) :
    Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (armPorts A B)) :=
  .cons saved (.cons sum (.cons state .nil))

private def resultPorts (output : Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (results A))) :
    Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (results A)) :=
  .cons (output.get .head) (.cons (output.get (.tail .head)) (.cons (output.get (.tail (.tail .head))) .nil))

@[simp] private theorem fin_cases_one {F : Fin 2 → Sort*} (z : F 0) (s : (i : Fin 1) → F i.succ) :
    Fin.cases (motive := F) z s (1 : Fin 2) = s 0 :=
  Fin.cases_succ (motive := F) (0 : Fin 1)

private theorem arm_exit (s : Blocks Φ A B) (fuel : Nat) (saved a : TyDen A) (state : σ) :
    (arms s 0).1.run (runtimeModel (ε := ε)) fuel
      (armInput (B := B) saved ((TypeModel.coprodEquiv A B).symm (.inl a)) state) =
      some (bodyResult (.inl a, state)) := by
  change some (bodyResult (.inl (Sum.elim id (fun _ => saved)
    (TypeModel.coprodEquiv A B ((TypeModel.coprodEquiv A B).symm (.inl a)))), state)) = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem arm_restart (s : Blocks Φ A B) (fuel : Nat) (saved : TyDen A) (b : TyDen B) (state : σ) :
    (arms s 1).1.run (runtimeModel (ε := ε)) fuel
      (armInput (B := B) saved ((TypeModel.coprodEquiv A B).symm (.inr b)) state) =
      some (bodyResult (.inr ((call (ε := ε) (m := StateM σ) s.body b).run state).1,
        ((call (ε := ε) (m := StateM σ) s.body b).run state).2)) := by
  simp only [arms, fin_cases_one]
  change some (resultPorts (A := A) (decode (((match
    TypeModel.coprodEquiv A B ((TypeModel.coprodEquiv A B).symm (.inr b)) with
    | .inl _ => pure (loopResult 1 saved)
    | .inr payload => call (ε := ε) s.body payload >>= fun a => pure (loopResult 1 a)) :
      StateM σ _).run state))) = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem body_run (s : Blocks Φ A B) (fuel : Nat) (a : TyDen A) (state : σ) :
    (thetaBody s).1.run (runtimeModel (ε := ε) (σ := σ)) fuel (point a state) =
      some (bodyResult ((round (ε := ε) (m := StateM σ) s a).run state)) := by
  change (let header := (headerAction (ε := ε) (m := StateM σ) s.header a).run state
          let tag : Fin 2 := match header.1 with | .inl _ => 0 | .inr _ => 1
          (arms s tag).1.run (runtimeModel (ε := ε)) fuel
            (armInput (B := B) a ((TypeModel.coprodEquiv A B).symm header.1) header.2) >>= fun output =>
            some (resultPorts output)) = _
  rw [show (round (ε := ε) (m := StateM σ) s a).run state =
    (let header := (headerAction (ε := ε) (m := StateM σ) s.header a).run state
     match header.1 with
     | .inl x => (.inl x, header.2)
     | .inr b =>
       let body := (call (ε := ε) (m := StateM σ) s.body b).run header.2
       (.inr body.1, body.2)) by
    rw [round, StateT.run_bind]
    obtain ⟨result, next⟩ := (headerAction (ε := ε) (m := StateM σ) s.header a).run state
    cases result <;> rfl]
  obtain ⟨result, next⟩ := (headerAction (ε := ε) (m := StateM σ) s.header a).run state
  cases result with
  | inl x =>
    change (arms s 0).1.run (runtimeModel (ε := ε)) fuel
      (armInput (B := B) a ((TypeModel.coprodEquiv A B).symm (.inl x)) next) >>= _ = _
    rw [arm_exit]
    rfl
  | inr b =>
    change (arms s 1).1.run (runtimeModel (ε := ε)) fuel
      (armInput (B := B) a ((TypeModel.coprodEquiv A B).symm (.inr b)) next) >>= _ = _
    rw [arm_restart]
    rfl

private theorem point_injective :
    Function.Injective (fun p : TyDen A × σ => point p.1 p.2) := by
  apply Function.LeftInverse.injective (g := fun x =>
    (x.get .head, x.get (.tail .head)))
  rintro ⟨a, state⟩
  rfl

private theorem graph_run (s : Blocks Φ A B) (fuel : Nat) (a : TyDen A) (state : σ) :
    (graph s).run (runtimeModel (ε := ε) (σ := σ)) fuel (point a state) =
      NestedTheta.iterate (fun input => (thetaBody s).1.run (runtimeModel (ε := ε) (σ := σ)) fuel input)
        (fun tag => tag.down.val == 1) fuel (point a state) := by
  rw [← NestedTheta.Graph.run_toTerm, graph, NestedTheta.Term.toTerm_toGraph]
  let run := NestedTheta.iterate (fun input => (thetaBody s).1.run (runtimeModel (ε := ε) (σ := σ)) fuel input)
    (fun tag => tag.down.val == 1) fuel (point a state)
  let wires : Wires (Threaded (carried A)) [Threaded (carried A)] (Threaded (carried A)) :=
    withRuntime (nextRuntime [] (carried A)) (.cons (.output (0 : Fin 1) .head) .nil)
  change (do
    let result ← run
    some (wires.read (point a state : Tuple (RuntimeValues (TyDen (τ := τ)) σ) _)
      (Locals.snoc (past := []) (F := RuntimeValues (TyDen (τ := τ)) σ) PUnit.unit result))) = run
  cases run with
  | none => rfl
  | some output =>
    cases output with
    | cons x tail =>
      cases tail with
      | cons returned tail => cases tail; rfl

section

variable [InstructionModel Φ τ ε (StateT σ Part.{u})]

private theorem bounded (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (s : Blocks Φ A B) (bodyFuel fuel : Nat) (input output : TyDen A × σ) :
    output ∈ Silmaril.Elgot.Part.runFor (Silmaril.Elgot.StateT.body (round (ε := ε) s)) fuel input ↔
      NestedTheta.iterate (fun x => (thetaBody s).1.run (runtimeModel (ε := ε) (σ := σ)) bodyFuel x)
        (fun tag => tag.down.val == 1) fuel (point input.1 input.2) = some (point output.1 output.2) := by
  induction fuel generalizing input with
  | zero => simp [Silmaril.Elgot.Part.runFor, NestedTheta.iterate]
  | succ fuel ih =>
    rw [Silmaril.Elgot.Part.runFor, NestedTheta.iterate, body_run]
    simp only [Silmaril.Elgot.StateT.body, round_run agrees, Part.bind_eq_bind,
      Part.bind_some, Function.comp_apply, Part.pure_eq_some]
    obtain ⟨result, next⟩ := (round (ε := ε) (m := StateM σ) s input.1).run input.2
    cases result with
    | inl a =>
      change output ∈ Part.some (a, next) ↔ some (point a next) = some (point output.1 output.2)
      rw [Part.mem_some_iff, Option.some.injEq]
      exact eq_comm.trans (point_injective (A := A) (σ := σ)).eq_iff.symm
    | inr a => exact ih (a, next)

theorem returns_iff (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (s : Blocks Φ A B) (a b : TyDen A) (initial final : σ) :
    (iter (round (ε := ε) (m := StateT σ Part.{u}) s) a).run initial = Part.some (b, final) ↔
      (graph s).Returns (wireModel (ε := ε)).toRVSDG (point a initial) (point b final) := by
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff_exists_fuel]
  change (∃ _, _) ↔ ∃ fuel, (graph s).run _ fuel _ = some _
  exact exists_congr fun fuel => by
    rw [graph_run]
    exact bounded agrees s fuel fuel (a, initial) (b, final)

end

open Isotope.LambdaSSA.Semantics.Monadic (Env LabelDen)
open OrderedTheta (exit exitValue)

private theorem boundary_injective :
    Function.Injective (fun output : Tuple (Values (TyDen (τ := τ))) (Threaded (carried A)) × σ =>
      (exit (output.1.get .head), output.2)) := by
  have eta (xs : Tuple (Values (TyDen (τ := τ))) (Threaded (carried A))) :
      xs = .cons (xs.get .head) (.cons PUnit.unit .nil) := by
    cases xs with
    | cons x xs =>
      cases xs with
      | cons slot xs => cases slot; cases xs; rfl
  rintro ⟨xs, state⟩ ⟨ys, final⟩ h
  have dataEq := congrArg (fun p : LabelDen [A] × σ => exitValue p.1) h
  have tokenEq := congrArg Prod.snd h
  change xs.get .head = ys.get .head at dataEq
  let packData (x : TyDen A) : Tuple (Values (TyDen (τ := τ))) (Threaded (carried A)) :=
    .cons x (.cons PUnit.unit .nil)
  exact Prod.ext ((eta xs).trans ((congrArg packData dataEq).trans (eta ys).symm)) tokenEq

theorem erased_iff (s : Blocks Φ A B) (a b : TyDen A) (initial final : σ) :
    erasedObservation (ε := ε) s a initial = Part.some (exit b, final) ↔
      (graph s).Returns (wireModel (ε := ε)).toRVSDG (point a initial) (point b final) := by
  let out := NestedTheta.ExplicitRuntime.boundaryResult (outs := carried A) (point b final)
  have h := NestedTheta.ExplicitRuntime.observe_eq_some
    (wireModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)) (graph s) (graphChecked s) (point a initial) (point b final)
  rw [← h, erasedObservation, Part.eq_some_iff, Part.eq_some_iff]
  change (exit b, final) ∈ Part.map
    (fun output : Tuple (Values (TyDen (τ := τ))) (Threaded (carried A)) × σ =>
      (exit (output.1.get .head), output.2)) _ ↔ out ∈ _
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨output, member, eq⟩
    have same := boundary_injective (A := A) (σ := σ) (a₁ := output) (a₂ := out) eq
    exact same ▸ member
  · intro member
    exact ⟨out, member, rfl⟩

variable [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem erased_denote (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A} (rel : Related A B r g) (env : Env [A]) (state : σ) :
    erasedObservation (ε := ε) rel.instructions env.2 state =
      (TwoBlock.denote (ε := ε) (m := StateT σ Part.{u}) g env).run state := by
  rw [rel.denote_iter, StateT.run_bind]
  apply Part.ext
  rintro ⟨label, final⟩
  cases label with
  | inr impossible => exact nomatch impossible
  | inl b =>
    change (exit b, final) ∈ erasedObservation (ε := ε) rel.instructions env.2 state ↔ _
    rw [← Part.eq_some_iff, erased_iff, ← returns_iff agrees, Part.eq_some_iff]
    change (b, final) ∈ (iter (round (ε := ε) (m := StateT σ Part.{u}) rel.instructions) env.2).run state ↔
      (exit b, final) ∈ ((iter (round (ε := ε) (m := StateT σ Part.{u}) rel.instructions) env.2).run state).bind
        (fun p => Part.some (exit p.1, p.2))
    rw [Part.mem_bind_iff]
    constructor
    · intro member
      exact ⟨(b, final), member, Part.mem_some_iff.mpr rfl⟩
    · rintro ⟨⟨value, token⟩, member, eq⟩
      have same := congrArg (fun p : LabelDen [A] × σ => (exitValue p.1, p.2)) (Part.mem_some_iff.mp eq)
      exact same.symm ▸ member

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Proofs
