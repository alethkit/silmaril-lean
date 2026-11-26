module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.SSA.PhiView.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA

open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes
open Loop Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env InstrDeterministic extend)

universe u v

variable (m : Diamond.Model.{0,0,u} Op) {σ : Type v}
variable (args : Inputs (Word m))

private theorem instr_deterministic : InstrDeterministic (instruction m (σ := σ)) := by
  intro code arg start a finish b finish' left right
  exact ⟨Option.some.inj (left.1.symm.trans right.1), left.2.trans right.2.symm⟩

theorem lower_hasType : lower.HasType inputContext [returnType] := by
  refine .cfg (fun _ => carriedType) ?_ (fun _ => ?_)
  · exact .let₁ (.op .unit) (.br rfl (PhiView.packTerm_hasType entryArgs))
  · refine .let₂ (A := wordCode) (B := PhiView.packedType [wordCode, wordCode]) (.var (i := 0) rfl) ?_
    refine .let₂ (A := wordCode) (B := returnType) (.var (i := 0) rfl) ?_
    refine .let₂ (A := wordCode) (B := .unit) (.var (i := 0) rfl) ?_
    refine .let₁ (.op (.pair (.var (i := 1) rfl) (.pair (.var (i := 7) rfl) .unit))) ?_
    refine .let₁ (.op (.pair (.var (i := 2) rfl) .unit)) ?_
    refine .let₁ (.op (.pair (.var (i := 7) rfl) (.pair (.var (i := 5) rfl) .unit))) ?_
    exact .case (.var (i := 2) rfl)
      (.br rfl (PhiView.packTerm_hasType backedgeArgs)) (.br rfl (PhiView.packTerm_hasType exitArgs))

theorem edge_transfer_iff (arrival : Incoming) (old : Env (Word m)) (start finish : σ)
    (label : Nat) (payload : Value (Word m)) :
    Semantics.Region.Eval (instruction m) old (.br (edge arrival).target (edge arrival).argument)
        start label payload finish ↔
      label = 0 ∧ payload = latchPayload m arrival old ∧ finish = start := by
  rw [PhiView.latch_eq_transfer (instruction m) phiView]
  cases arrival <;> rfl

theorem entry_eval (start : σ) :
    Semantics.Region.Eval (instruction m) (inputEnv m args) entry start 0
      (packCarried m (graph.initial m (input m args))) start := by
  refine .let₁ (va := .atom (seed m)) (.op .unit ⟨rfl, rfl⟩) ?_
  apply (edge_transfer_iff m .entry _ _ _ _ _).mpr
  exact ⟨rfl, rfl, rfl⟩

private theorem header_eval_carried (a b i : Word m) (start : σ) :
    Semantics.Region.Eval (instruction m) (extend (inputEnv m args) (packCarried m (carried m a b i)))
        header start (stepLabel m (graph.step m (input m args) (carried m a b i)))
          (stepPayload m (graph.step m (input m args) (carried m a b i))) start := by
  change Semantics.Region.Eval (instruction m) _ header start
    (stepLabel m (if test m i args.limit then .inr (carried m b a (advance m i)) else .inl (observe m a b)))
    (stepPayload m (if test m i args.limit then .inr (carried m b a (advance m i)) else .inl (observe m a b)))
    start
  refine .let₂ .var (.let₂ .var (.let₂ .var ?_))
  refine .let₁ (va := selector m (test m i args.limit)) (.op (.pair .var (.pair .var .unit)) ⟨rfl, rfl⟩) ?_
  refine .let₁ (va := .atom (advance m i)) (.op (.pair .var .unit) ⟨rfl, rfl⟩) ?_
  refine .let₁ (va := .atom (observe m a b)) (.op (.pair .var (.pair .var .unit)) ⟨rfl, rfl⟩) ?_
  cases test m i args.limit with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, stepLabel, stepPayload, selector]
    exact .case_inr .var (.br (.pair .var .unit))
  | true =>
    simp only [↓reduceIte, stepLabel, stepPayload, selector]
    refine .case_inl .var ?_
    apply (edge_transfer_iff m .backedge _ _ _ _ _).mpr
    exact ⟨rfl, rfl, rfl⟩

theorem header_eval (old : Carried m) (start : σ) :
    Semantics.Region.Eval (instruction m) (extend (inputEnv m args) (packCarried m old))
        header start (stepLabel m (graph.step m (input m args) old))
          (stepPayload m (graph.step m (input m args) old)) start := by
  cases old with
  | cons a rest =>
    cases rest with
    | cons b rest =>
      cases rest with
      | cons i rest =>
        cases rest
        exact header_eval_carried m args a b i start

private theorem follow_of_returns {old : Carried m} {count : Nat} {result : Word m}
    (h : graph.ReturnsAfter (out := word) m (input m args) count old result) (start : σ) :
    Semantics.Region.Follow (instruction m) (inputEnv m args) blocks
      0 (packCarried m old) start 0 (packResult m result) start := by
  refine Graph.ReturnsAfter.rec (out := word) (motive := fun _ old result _ =>
    Semantics.Region.Follow (instruction m) (inputEnv m args) blocks
      0 (packCarried m old) start 0 (packResult m result) start) ?_ ?_ h
  · intro old _ taken
    have round := header_eval m args old start
    rw [taken] at round
    exact .step (by decide) round (.exit (Nat.le_refl 1))
  · intro _ old _ _ taken _ ih
    have round := header_eval m args old start
    rw [taken] at round
    exact .step (by decide) round ih

private theorem returns_of_follow {env : Env (Word m)} {n : Nat} {code : Fin n → Region Opcode}
    {first label : Nat} {current payload : Value (Word m)} {start finish : σ}
    (h : Semantics.Region.Follow (instruction m) env code first current start label payload finish)
    (envEq : env = inputEnv m args) (sizeEq : n = 1) (bodyEq : ∀ i, code i = header)
    (atHeader : first = 0) (old : Carried m) (currentEq : current = packCarried m old) :
    ∃ count result, graph.ReturnsAfter m (input m args) count old result ∧
      label = 0 ∧ payload = packResult m result ∧ finish = start := by
  refine Semantics.Region.Follow.rec
    (motive_1 := fun _ _ _ _ _ _ _ => True)
    (motive_2 := fun env {n} code first current start label payload finish _ =>
      env = inputEnv m args → n = 1 → (∀ i, code i = header) → first = 0 →
        ∀ old, current = packCarried m old →
          ∃ count result, graph.ReturnsAfter m (input m args) count old result ∧
            label = 0 ∧ payload = packResult m result ∧ finish = start)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?_ ?_ h envEq sizeEq bodyEq atHeader old currentEq
  · intro _ _ _ _ _ _ outside _ sizeEq _ atHeader _ _
    omega
  · intro _ _ _ _ _ _ _ _ _ start _ _ _ round rest _ ih envEq sizeEq bodyEq _ old currentEq
    rw [envEq, currentEq, bodyEq] at round
    have observed := round.deterministic (instr_deterministic m) (header_eval m args old start)
    cases taken : graph.step m (input m args) old with
    | inl result =>
      simp only [taken, stepLabel, stepPayload] at observed
      obtain ⟨rfl, rfl, rfl⟩ := observed
      cases rest with
      | exit _ => exact ⟨0, result, .exit taken, by omega, rfl, rfl⟩
      | step impossible _ _ => omega
    | inr next =>
      simp only [taken, stepLabel, stepPayload] at observed
      obtain ⟨rfl, rfl, rfl⟩ := observed
      obtain ⟨count, result, returned, out, value, state⟩ :=
        ih envEq sizeEq bodyEq rfl next rfl
      exact ⟨count + 1, result, .backedge taken returned, out, value, state⟩

theorem follow_iff (old : Carried m) (start finish : σ) (label : Nat) (payload : Value (Word m)) :
    Semantics.Region.Follow (instruction m) (inputEnv m args) blocks
        0 (packCarried m old) start label payload finish ↔
      ∃ count result, graph.ReturnsAfter m (input m args) count old result ∧
        label = 0 ∧ payload = packResult m result ∧ finish = start := by
  constructor
  · intro h
    exact returns_of_follow m args h rfl rfl (fun _ => rfl) rfl old rfl
  · rintro ⟨_, result, returned, rfl, rfl, same⟩
    subst finish
    exact follow_of_returns m args returned start

theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Word m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m args) lower start label payload finish ↔
      ∃ result, graph.Returns m (input m args) result ∧
        label = 0 ∧ payload = packResult m result ∧ finish = start := by
  constructor
  · intro eval
    cases eval with
    | cfg entryRun followRun =>
      obtain ⟨rfl, rfl, rfl⟩ := entryRun.deterministic (instr_deterministic m) (entry_eval m args start)
      obtain ⟨count, result, returned, out, value, state⟩ := (follow_iff m args _ _ _ _ _).mp followRun
      exact ⟨result, ⟨count, returned⟩, out, value, state⟩
  · rintro ⟨result, ⟨count, returned⟩, rfl, rfl, same⟩
    subst finish
    exact .cfg (entry_eval m args start) (follow_of_returns m args returned start)

theorem returns_iff (start : σ) (result : Word m) :
    graph.Returns m (input m args) result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m args) lower start 0 (packResult m result) start := by
  rw [lower_eval_iff]
  constructor
  · intro returned
    exact ⟨result, returned, rfl, rfl, rfl⟩
  · rintro ⟨other, returned, _, same, _⟩
    obtain rfl := Value.atom.inj (Value.pair.inj same).1
    exact returned

end Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA
