module

public import Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Activation
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes
open Loop Loop.LambdaSSA.Generic
open Diamond (Model Val ValueSort dataPorts sortValue)
open Diamond.LambdaSSA (Atom Primitive encode encodeTuple inputEnv instruction
  encode_injective instruction_deterministic)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}
variable (m : Model.{u,v,w} Op) (g : Graph Op inputs carried entrySigs headerSigs out)
variable (input : Tuple (Val m.value) (dataPorts inputs))

private theorem follow_of_returns {old : Tuple (Val m.value) (dataPorts carried)} {count : Nat}
    {result : sortValue m.value out} (returned : g.ReturnsAfter m input count old result) (start : σ) :
    Semantics.Region.Follow (instruction m) (inputEnv m input) (blocks g)
      0 (encodeTuple m old) start 0 (packResult m result) start := by
  refine Graph.ReturnsAfter.rec (motive := fun _ old result _ =>
    Semantics.Region.Follow (instruction m) (inputEnv m input) (blocks g)
      0 (encodeTuple m old) start 0 (packResult m result) start) ?_ ?_ returned
  · intro old _ taken
    have round := header_eval m g input old start
    rw [taken] at round
    exact .step (by decide) round (.exit (Nat.le_refl 1))
  · intro _ old _ _ taken _ ih
    have round := header_eval m g input old start
    rw [taken] at round
    exact .step (by decide) round ih

private theorem returns_of_follow {env : Env (Atom m)} {n : Nat} {code : Fin n → Region (Primitive Op)}
    {first label : Nat} {current payload : Value (Atom m)} {start finish : σ}
    (h : Semantics.Region.Follow (instruction m) env code first current start label payload finish)
    (envEq : env = inputEnv m input) (sizeEq : n = 1) (bodyEq : ∀ i, code i = header g)
    (atHeader : first = 0) (old : Tuple (Val m.value) (dataPorts carried))
    (currentEq : current = encodeTuple m old) :
    ∃ count result, g.ReturnsAfter m input count old result ∧
      label = 0 ∧ payload = packResult m result ∧ finish = start := by
  refine Semantics.Region.Follow.rec
    (motive_1 := fun _ _ _ _ _ _ _ => True)
    (motive_2 := fun env {n} code first current start label payload finish _ =>
      env = inputEnv m input → n = 1 → (∀ i, code i = header g) → first = 0 →
        ∀ old, current = encodeTuple m old →
          ∃ count result, g.ReturnsAfter m input count old result ∧
            label = 0 ∧ payload = packResult m result ∧ finish = start)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?_ ?_ h envEq sizeEq bodyEq atHeader old currentEq
  · intro _ _ _ _ _ _ outside _ sizeEq _ atHeader _ _
    omega
  · intro _ _ _ _ _ _ _ _ _ start _ _ _ round rest _ ih envEq sizeEq bodyEq _ old currentEq
    rw [envEq, currentEq, bodyEq] at round
    have observed := round.deterministic (instruction_deterministic m) (header_eval m g input old start)
    cases taken : g.step m input old with
    | inl result =>
      simp only [taken, stepLabel, stepPayload] at observed
      obtain ⟨rfl, rfl, rfl⟩ := observed
      cases rest with
      | exit _ => exact ⟨0, result, .exit taken, by omega, rfl, rfl⟩
      | step impossible _ _ => omega
    | inr next =>
      simp only [taken, stepLabel, stepPayload] at observed
      obtain ⟨rfl, rfl, rfl⟩ := observed
      obtain ⟨count, result, returned, out, value, state⟩ := ih envEq sizeEq bodyEq rfl next rfl
      exact ⟨count + 1, result, .backedge taken returned, out, value, state⟩

theorem follow_iff (old : Tuple (Val m.value) (dataPorts carried))
    (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Follow (instruction m) (inputEnv m input) (blocks g)
        0 (encodeTuple m old) start label payload finish ↔
      ∃ count result, g.ReturnsAfter m input count old result ∧
        label = 0 ∧ payload = packResult m result ∧ finish = start := by
  constructor
  · intro h
    exact returns_of_follow m g input h rfl rfl (fun _ => rfl) rfl old rfl
  · rintro ⟨_, result, returned, rfl, rfl, same⟩
    subst finish
    exact follow_of_returns m g input returned start

theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m input) (lower g) start label payload finish ↔
      ∃ result, g.Returns m input result ∧ label = 0 ∧ payload = packResult m result ∧ finish = start := by
  constructor
  · intro eval
    cases eval with
    | cfg entryRun followRun =>
      obtain ⟨rfl, rfl, rfl⟩ := entryRun.deterministic (instruction_deterministic m) (entry_eval m g input start)
      obtain ⟨count, result, returned, out, value, state⟩ := (follow_iff m g input _ _ _ _ _).mp followRun
      exact ⟨result, ⟨count, returned⟩, out, value, state⟩
  · rintro ⟨result, ⟨count, returned⟩, rfl, rfl, same⟩
    subst finish
    exact .cfg (entry_eval m g input start) (follow_of_returns m g input returned start)

theorem returns_iff (start : σ) (result : sortValue m.value out) :
    g.Returns m input result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m input) (lower g) start 0 (packResult m result) start := by
  rw [lower_eval_iff]
  constructor
  · intro returned
    exact ⟨result, returned, rfl, rfl, rfl⟩
  · rintro ⟨other, returned, _, same, _⟩
    obtain rfl := encode_injective m (Value.pair.inj same).1
    exact returned

end Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic
