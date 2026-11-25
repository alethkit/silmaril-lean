module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton.Proofs

open OrderedTheta (carried results carriedData)
open OrderedRuntime.Structured
open Silmaril.Elgot (iter)

universe u
variable {τ σ X Y : Type u}
variable {P E : Dialect.{u,u} τ PUnit} {K R : τ}
variable (header : OrderedRuntime.Structured.Instruction P E (carried K) (headerPorts R))
variable (arms : Fin 2 → Closed P E (armData K R) (OrderedTheta.resultData K) [Threaded (results K)])
variable (m : OrderedRuntime.Structured.Model P E (StateM σ))

set_option backward.isDefEq.respectTransparency false

theorem graph_run (fuel : Nat) (a : m.value K) (state : σ) :
    (graph header arms).run m.toRVSDG fuel (point a state) =
      NestedTheta.iterate (fun input => (thetaBody header arms).1.run m.toRVSDG fuel input)
        (fun tag => tag.down.val == 1) fuel (point a state) := by
  rw [← NestedTheta.Graph.run_toTerm, graph, NestedTheta.Term.toTerm_toGraph]
  let run := NestedTheta.iterate (fun input => (thetaBody header arms).1.run m.toRVSDG fuel input)
    (fun tag => tag.down.val == 1) fuel (point a state)
  let wires : Wires (Threaded (carried K)) [Threaded (carried K)] (Threaded (carried K)) :=
    withRuntime (nextRuntime [] (carried K)) (.cons (.output (0 : Fin 1) .head) .nil)
  change (do
    let result ← run
    some (wires.read (point a state)
      (Locals.snoc (past := []) (F := RuntimeValues m.value σ) PUnit.unit result))) = run
  cases run with
  | none => rfl
  | some output =>
    cases output with
    | cons a tail =>
      cases tail with
      | cons returned tail => cases tail; rfl

theorem observeCarrier_iff (a b : m.value K) (initial final : σ) :
    observeCarrier header arms m a initial = Part.some (b, final) ↔
      (graph header arms).Returns m.toRVSDG (point a initial) (point b final) := by
  let project := fun out : Tuple (Values m.value) (Threaded (carried K)) × σ =>
    (out.1.get .head, out.2)
  have leftInverse : Function.LeftInverse (fun p : m.value K × σ =>
      (Tuple.cons (F := Values m.value) (t := .value K) p.1 (.cons (t := runtime) PUnit.unit .nil), p.2)) project := by
    rintro ⟨xs, state⟩
    cases xs with
    | cons a xs =>
      cases xs with
      | cons slot xs => cases slot; cases xs; rfl
  let out := NestedTheta.ExplicitRuntime.boundaryResult (outs := carried K) (point b final)
  rw [← NestedTheta.ExplicitRuntime.observe_eq_some m (graph header arms)
    (graphChecked header arms) (point a initial) (point b final), observeCarrier,
    Part.eq_some_iff, Part.eq_some_iff]
  change (b, final) ∈ Part.map project _ ↔ out ∈ _
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨output, member, eq⟩
    have same : output = out := leftInverse.injective eq
    exact same ▸ member
  · intro member
    exact ⟨out, member, rfl⟩

variable (enter : X → m.value K) (finish : Y → m.value K)
variable (f : X → StateT σ Part (Y ⊕ X))
variable (step : X × σ → (Y ⊕ X) × σ)
variable (stepLift : ∀ input : X × σ, (f input.1).run input.2 = Part.some (step input))
variable (stepWire : ∀ (fuel : Nat) (input : X × σ),
  (thetaBody header arms).1.run m.toRVSDG fuel (point (enter input.1) input.2) =
    some (tagged enter finish (step input)))

include stepLift stepWire in
private theorem bounded (bodyFuel fuel : Nat) (input : X × σ) (output : m.value K × σ) :
    output ∈ Part.map (fun p => (finish p.1, p.2))
        (Silmaril.Elgot.Part.runFor (Silmaril.Elgot.StateT.body f) fuel input) ↔
      NestedTheta.iterate (fun x => (thetaBody header arms).1.run m.toRVSDG bodyFuel x)
        (fun tag => tag.down.val == 1) fuel (point (enter input.1) input.2) =
          some (point output.1 output.2) := by
  induction fuel generalizing input with
  | zero => simp [Silmaril.Elgot.Part.runFor, NestedTheta.iterate]
  | succ fuel ih =>
    rw [Silmaril.Elgot.Part.runFor, NestedTheta.iterate, stepWire]
    simp only [Silmaril.Elgot.StateT.body, stepLift, Part.bind_eq_bind,
      Part.bind_some, Function.comp_apply, Part.pure_eq_some]
    obtain ⟨result, next⟩ := step input
    cases result with
    | inl out =>
      change output ∈ Part.map _ (Part.some (out, next)) ↔
        some (point (finish out) next) = some (point output.1 output.2)
      rw [Part.map_some, Part.mem_some_iff, Option.some.injEq, eq_comm]
      have injective : Function.Injective (fun p : m.value K × σ => point p.1 p.2) := by
        apply Function.LeftInverse.injective (g := fun x => (x.get .head, x.get (.tail .head)))
        rintro ⟨b, state⟩
        rfl
      exact injective.eq_iff.symm
    | inr nextInput => exact ih (nextInput, next)

include stepLift stepWire in
theorem observeCarrier_iter (input : X × σ) :
    observeCarrier header arms m (enter input.1) input.2 =
      Part.map (fun out => (finish out.1, out.2)) ((iter f input.1).run input.2) := by
  apply Part.ext
  intro output
  rw [← Part.eq_some_iff]
  have observes := observeCarrier_iff header arms m (enter input.1) output.1 input.2 output.2
  rw [observes, Silmaril.Elgot.StateT.run_iter, Part.mem_map_iff]
  change (∃ fuel, (graph header arms).run m.toRVSDG fuel _ = some _) ↔ _
  constructor
  · rintro ⟨fuel, ran⟩
    rw [graph_run] at ran
    obtain ⟨out, member, eq⟩ := (Part.mem_map_iff _).mp
      ((bounded header arms m enter finish f step stepLift stepWire fuel fuel input output).mpr ran)
    exact ⟨out, (Silmaril.Elgot.Part.mem_iter_iff_exists_fuel _ _ _).mpr ⟨fuel, member⟩, eq⟩
  · rintro ⟨out, member, eq⟩
    obtain ⟨fuel, ran⟩ := (Silmaril.Elgot.Part.mem_iter_iff_exists_fuel _ _ _).mp member
    refine ⟨fuel, ?_⟩
    rw [graph_run]
    exact (bounded header arms m enter finish f step stepLift stepWire fuel fuel input output).mp
      ((Part.mem_map_iff _).mpr ⟨out, ran, eq⟩)

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton.Proofs
