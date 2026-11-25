module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Thms
public import Silmaril.Semantics.ElgotMonads.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Proofs

open Silmaril.Elgot
open OrderedRuntime.Structured (Values Ty Instruction)

universe u v w k
variable {V : Type u} {A : Signature.{u,v} V} {σ : Type (max u w)}
variable {args ins outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ρ : Type k}

private def keep {X : Type k} (p : Part X) : _root_.StateT ρ Part X :=
  _root_.StateT.mk fun s => Part.map (fun x => (x, s)) p

private theorem keep_run {X : Type k} (p : Part X) (s : ρ) :
    (keep p).run s = Part.map (fun x => (x, s)) p := rfl

private theorem keep_bind {X Y : Type k} (p : Part X) (q : X → Part Y) :
    keep (ρ := ρ) (p >>= q) = keep p >>= fun x => keep (q x) := by
  apply _root_.StateT.ext
  intro s
  simp only [_root_.StateT.run_bind, keep_run, Part.bind_eq_bind, Part.bind_map, Part.map_bind]

private theorem keep_step {X Y : Type k} (step : X → Part (Y ⊕ X)) (x : X) (s : ρ) :
    Silmaril.Elgot.StateT.body (fun a => keep (ρ := ρ) (step a)) (x, s) =
      Part.map (fun r => Silmaril.Elgot.StateT.distribute (r, s)) (step x) := by
  change (keep (step x)).run s >>= (pure ∘ Silmaril.Elgot.StateT.distribute) = _
  simp only [keep_run, Part.bind_eq_bind, Part.bind_map, Function.comp_apply, Part.pure_eq_some,
    Part.bind_some_eq_map]

/-- Transport iteration along the fixed-store embedding of its carried
values. Uniformity reuses the source schedule at every activation. -/
private theorem keep_iter {X Y : Type k} (step : X → Part (Y ⊕ X)) (x : X) :
    keep (ρ := ρ) (iter step x) = iter (fun a => keep (step a)) x := by
  apply _root_.StateT.ext
  intro store
  let finish : Y → Part (Y × ρ) := fun y => Part.some (y, store)
  let embed : X → X × ρ := fun z => (z, store)
  let body := Silmaril.Elgot.StateT.body (fun a => keep (ρ := ρ) (step a))
  have square : (mapReturn step finish >=> liftPure (Sum.map id embed)) = (liftPure embed >=> body) := by
    funext a
    change (mapReturn step finish a >>= fun r => pure (Sum.map id embed r)) = (pure (embed a) >>= body)
    rw [pure_bind]
    change _ = Silmaril.Elgot.StateT.body (fun a => keep (ρ := ρ) (step a)) (a, store)
    rw [keep_step]
    simp only [mapReturn, Part.bind_eq_bind, Part.bind_assoc]
    rw [← Part.bind_some_eq_map]
    congr 1
    funext result
    cases result <;> simp [finish, embed, Silmaril.Elgot.StateT.distribute, Part.pure_eq_some, Part.bind_some]
  have changeState := congrFun (LawfulElgotMonad.uniformity _ _ _ square) x
  have changeReturn := congrFun (LawfulElgotMonad.naturality step finish) x
  change (keep (iter step x)).run store = (iter (fun a => keep (step a)) x).run store
  rw [keep_run, Silmaril.Elgot.StateT.run_iter]
  exact (by simpa only [Bind.kleisliRight, finish, Part.bind_eq_bind, Part.bind_some_eq_map] using changeReturn :
    Part.map (fun y => (y, store)) (iter step x) = iter (mapReturn step finish) x).trans
    (by simpa only [Bind.kleisliRight, liftPure, pure_bind, Function.comp_apply, embed, body] using changeState)

private theorem kind_keep (m : Institution.Partial.Model.{u,v,w} A.ordered σ) (kind : Kind A.op ins outs)
    (child : Fin kind.arity → Tuple (Values m.value) kind.entry → Part (Tuple (Values m.value) kind.exit))
    (input : Tuple (Values m.value) ins) :
    kind.denoteWith (OrderedState.Partial.interpretation m)
      (fun j x => keep (child j x)) input = keep (kind.denoteWith (forgetStore m).partial child input) := by
  cases kind with
  | base shape =>
    cases shape with
    | simple op => cases op with
      | pure _ => rfl
      | effect op => exact PEmpty.elim op
    | gamma _ => cases input; rfl
  | theta =>
    change iter (stepWith (fun x => keep (child (0 : Fin 1) x))) input = keep (iter (stepWith (child (0 : Fin 1))) input)
    rw [keep_iter]
    congr 1

private theorem term_keep (m : Institution.Partial.Model.{u,v,w} A.ordered σ) (t : Term A.op args past sigs outs)
    (input : Tuple (Values m.value) args) (locals : Locals (Values m.value) past) :
    t.denoteOpenWith (OrderedState.Partial.interpretation m) input locals =
      keep (t.denoteOpenWith (forgetStore m).partial input locals) := by
  induction t with
  | ret => rfl
  | bind node children rest ihChildren ihRest =>
    simp only [Term.denoteOpenWith, ihChildren, ihRest, kind_keep, keep_bind]
    rfl

theorem observe_forget (m : Institution.Partial.Model.{u,v,w} A.ordered σ)
    (g : Graph A.op args [] sigs outs) (input : Tuple (Values m.value) args) (initial : σ) :
    OrderedState.Partial.observe m g input initial =
      Part.map (fun output => (output, initial)) (observe (forgetStore m) g input) := by
  unfold OrderedState.Partial.observe OrderedState.Partial.runOpen observe NestedTheta.Partial.observe
  rw [term_keep, keep_run]
  rfl

theorem returns_iff (m : Institution.Partial.Model.{u,v,w} A.ordered σ)
    (g : Graph A.op args [] sigs outs) (input : Tuple (Values m.value) args)
    (initial final : σ) (output : Tuple (Values m.value) outs) :
    (output, final) ∈ OrderedState.Partial.observe m g input initial ↔
      output ∈ observe (forgetStore m) g input ∧ final = initial := by
  rw [observe_forget, Part.mem_map_iff]
  constructor
  · rintro ⟨result, returned, equal⟩
    cases equal
    exact ⟨returned, rfl⟩
  · rintro ⟨returned, rfl⟩
    exact ⟨output, returned, rfl⟩

theorem diverges_iff (m : Institution.Partial.Model.{u,v,w} A.ordered σ)
    (g : Graph A.op args [] sigs outs) (input : Tuple (Values m.value) args) (initial : σ) :
    OrderedState.Partial.abnormal m g input initial .diverges ↔ Diverges (forgetStore m) g input := by
  constructor
  · intro divergent returned
    have good : (observe (forgetStore m) g input).get returned ∈ observe (forgetStore m) g input :=
      Part.get_mem returned
    have exactReturn := (returns_iff m g input initial initial _).mpr ⟨good, rfl⟩
    exact OrderedState.Partial.return_excludes_abnormal m g input initial exactReturn _ divergent
  · intro absent
    rcases OrderedState.Partial.endpoint_exists m g input initial with done | ⟨obs, seen⟩
    · have exactReturn := Part.get_mem done
      rcases eq : (OrderedState.Partial.observe m g input initial).get done with ⟨x, final⟩
      rw [eq] at exactReturn
      exact (absent ((returns_iff m g input initial final x).mp exactReturn).1.1).elim
    · cases obs with
      | diverges => exact seen
      | blocked b => exact PEmpty.elim b.opcode

theorem included_holds [Nonempty σ] (e : Equation A) (m : Institution.Partial.Model.{u,v,w} A.ordered σ) :
    Institution.Partial.Equation.Holds e.val m ↔ e.Holds (forgetStore m) := by
  constructor
  · intro ordered input
    obtain ⟨store⟩ := ‹Nonempty σ›
    have h := (ordered input store).1
    apply Part.ext
    intro output
    have left := returns_iff m e.val.lhs input store store output
    have right := returns_iff m e.val.rhs input store store output
    simp only [eq_self, and_true] at left right
    rw [← left, ← right, h]
  · intro stateless input store
    refine ⟨by rw [observe_forget, observe_forget, stateless input], ?_⟩
    intro obs
    cases obs with
    | blocked b => exact PEmpty.elim b.opcode
    | diverges =>
      rw [diverges_iff, diverges_iff]
      unfold Diverges
      rw [stateless input]

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Proofs
