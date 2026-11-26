module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms

/-! # Fold the actual two-header dispatcher using Elgot codiagonal -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Isotope.SSA (At)
open TwoBlock (localTypes)
open TwoBlock.TwoExit (callCase)
open Silmaril.Elgot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

section Iteration

variable {A B K D : Type u}

private def grouped (enter : A → m B) (inner : B → m (K ⊕ B)) (finish : K → m (D ⊕ A)) :
    (A ⊕ B) → m ((D ⊕ (A ⊕ B)) ⊕ (A ⊕ B))
  | .inl a => enter a >>= fun b => pure (.inr (.inr b))
  | .inr b => inner b >>= fun
    | .inl k => finish k >>= fun result => pure (.inl (Sum.map id Sum.inl result))
    | .inr b' => pure (.inr (.inr b'))

private theorem iterate_grouped (enter : A → m B) (inner : B → m (K ⊕ B)) (finish : K → m (D ⊕ A))
    (a : A) :
    iter (flattenBody (grouped enter inner finish)) (.inl a) =
      iter (fun x => enter x >>= iter inner >>= finish) a := by
  let complete := fun k => finish k >>= fun result => pure (Sum.map id (Sum.inl : A → A ⊕ B) result)
  have innerSquare : (mapReturn inner complete >=> liftPure (Sum.map id (Sum.inr : B → A ⊕ B))) =
      (liftPure (Sum.inr : B → A ⊕ B) >=> grouped enter inner finish) := by
    funext b
    simp only [Bind.kleisliRight, mapReturn, liftPure, Function.comp_apply, pure_bind, grouped, bind_assoc]
    congr 1
    funext result
    cases result <;> simp [complete]
  have innerPhase (b : B) : iter (grouped enter inner finish) (.inr b) = iter inner b >>= complete := by
    have h := congrFun (LawfulElgotMonad.uniformity _ _ _ innerSquare) b
    rw [← LawfulElgotMonad.naturality] at h
    simpa [Bind.kleisliRight, liftPure] using h.symm
  have outerSquare :
      ((fun x : A => enter x >>= iter inner >>= finish) >=> liftPure (Sum.map id (Sum.inl : A → A ⊕ B))) =
        (liftPure (Sum.inl : A → A ⊕ B) >=> iter (grouped enter inner finish)) := by
    funext x
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, bind_assoc]
    rw [congrFun (LawfulElgotMonad.fixpoint (grouped enter inner finish)) (.inl x)]
    simp only [grouped, bind_assoc, pure_bind, Sum.elim_inr, innerPhase, complete]
    rfl
  rw [← LawfulElgotMonad.codiagonal]
  simpa [Bind.kleisliRight, liftPure] using
    (congrFun (LawfulElgotMonad.uniformity _ _ _ outerSquare) a).symm

end Iteration

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε m]
variable {A B K D X Y : τ} {Γ L : List τ}

omit [Iterate m] [LawfulElgotMonad m] in
private theorem call_denotes (op : TwoBlock.Instruction Φ X Y) :
    Denotes (m := m) ε (op.typing Γ) (fun env => TwoBlock.call (ε := ε) op env.2) := by
  obtain ⟨op, rfl, rfl⟩ := op
  simpa [TwoBlock.call, Env.get, bind_pure] using
    Denotes.op (m := m) (ε := ε) (Denotes.var (Γ := instrSrc op :: Γ) (i := 0) rfl)

omit [LawfulElgotMonad m] in
private theorem jump_denotes {i : Nat} (h : At L i X) :
    RegionDenotes (m := m) ε (.br h (.var (Φ := Φ) (Γ := X :: Γ) (i := 0) rfl))
      (fun env => pure (LabelValue.inject i h env.2)) := by
  simpa only [Env.get, pure_bind, labelInject_eq_recursive] using
    RegionDenotes.br (m := m) (ε := ε) (h := h) (Denotes.var (Φ := Φ) (Γ := X :: Γ) (i := 0) rfl)

variable {extra : List τ}

private def externalExit (d : TyDen D) : LabelDen (D :: extra) := .inl d
private def outerTarget (a : TyDen A) : LabelDen (A :: B :: D :: extra) := .inl a
private def innerTarget (b : TyDen B) : LabelDen (A :: B :: D :: extra) := .inr (.inl b)
private def exitTarget (d : TyDen D) : LabelDen (A :: B :: D :: extra) := .inr (.inr (externalExit d))

variable (s : Loop Φ A B K D)

private def dispatchOuter (a : TyDen A) : m (LabelDen (A :: B :: D :: extra)) :=
  TwoBlock.call (ε := ε) s.enter a >>= fun b => pure (innerTarget b)

private def dispatchInner (b : TyDen B) : m (LabelDen (A :: B :: D :: extra)) :=
  callCase (ε := ε) s.inner b >>= fun
    | .inl k => callCase (ε := ε) s.finish k >>= fun result =>
      pure (Sum.elim exitTarget outerTarget result)
    | .inr next => pure (innerTarget next)

omit [LawfulElgotMonad m] in
private theorem outer_denotes :
    RegionDenotes (m := m) ε (outerTypingWithTail s extra) (fun env => dispatchOuter (ε := ε) s env.2) := by
  convert (by simpa only [labelInject_eq_recursive] using
    RegionDenotes.br (m := m) (ε := ε) (h := (rfl : At (A :: B :: D :: extra) 1 B)) (call_denotes (ε := ε) (m := m) (Γ := [A]) s.enter) :
    RegionDenotes (m := m) ε (outerTypingWithTail s extra)
      (fun env => TwoBlock.call (ε := ε) s.enter env.2 >>= fun b =>
        pure (LabelValue.inject 1 (rfl : At (A :: B :: D :: extra) 1 B) b))) using 1
  rfl

omit [LawfulElgotMonad m] in
private theorem inner_denotes :
    RegionDenotes (m := m) ε (innerTypingWithTail s extra) (fun env => dispatchInner (ε := ε) s env.2) := by
  have d := RegionDenotes.case (call_denotes (ε := ε) (m := m) (Γ := [A]) s.inner)
    (RegionDenotes.case (call_denotes (ε := ε) (m := m) (Γ := [B,A]) s.finish)
      (jump_denotes (ε := ε) (m := m) (Γ := [K,B,A]) (rfl : At (A :: B :: D :: extra) 2 D))
      (jump_denotes (ε := ε) (m := m) (Γ := [K,B,A]) (rfl : At (A :: B :: D :: extra) 0 A)))
    (jump_denotes (ε := ε) (m := m) (Γ := [B,A]) (rfl : At (A :: B :: D :: extra) 1 B))
  convert (show RegionDenotes (m := m) ε (innerTypingWithTail s extra) _ from d) using 1
  funext env
  simp only [dispatchInner, callCase, bind_assoc, pure_bind]
  congr 1
  funext v
  cases TypeModel.coprodEquiv K B v with
  | inl k =>
    apply congrArg (fun action => TwoBlock.call (ε := ε) (m := m) s.finish k >>= action)
    funext w
    cases TypeModel.coprodEquiv D A w <;> rfl
  | inr b => rfl

private def actions (i : Fin 2) : TyDen (localTypes A B i) → m (LabelDen (A :: B :: D :: extra)) :=
  Fin.cases (motive := fun j => TyDen (localTypes A B j) → m (LabelDen (A :: B :: D :: extra)))
    (dispatchOuter (ε := ε) s) (fun _ => dispatchInner (ε := ε) s) i

private def collect (p : Env [A] × FiniteLabelDen (localTypes A B)) : m (LabelDen (A :: B :: D :: extra)) :=
  actions (ε := ε) s p.2.1 p.2.2

omit [LawfulElgotMonad m] in
private theorem cfg_denotes :
    RegionDenotes (m := m) ε (regionTypingWithTail s extra)
      (cfgDenotation (R := localTypes A B) (fun env => pure (outerTarget env.2)) (collect (ε := ε) s)) := by
  apply RegionDenotes.cfg
  · exact jump_denotes (ε := ε) (m := m) (Γ := []) (rfl : At (A :: B :: D :: extra) 0 A)
  · intro i
    refine Fin.cases (motive := fun j => RegionDenotes (m := m) ε (blockTypingWithTail s j extra)
      (fun env => actions (ε := ε) s j env.2)) ?_ (fun j => ?_) i
    · exact outer_denotes (ε := ε) s
    · exact inner_denotes (ε := ε) s
  · exact ⟨fun _ _ _ => rfl⟩

private def injectLocal : (TyDen A ⊕ TyDen B) → LabelDen [A,B]
  | .inl a => .inl a
  | .inr b => .inr (.inl b)

private def flat : (TyDen A ⊕ TyDen B) → m (TyDen D ⊕ (TyDen A ⊕ TyDen B)) :=
  flattenBody (grouped (TwoBlock.call (ε := ε) s.enter) (callCase (ε := ε) s.inner)
    (callCase (ε := ε) s.finish))

private theorem denote_flat
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTypingWithTail s extra) env =
      iter (mapReturn (flat (ε := ε) s) (pure ∘ externalExit)) (.inl env.2) := by
  rw [TwoBlock.regionDenote_eq_of coherent (cfg_denotes (ε := ε) s)]
  simp only [cfgDenotation, pure_bind, binaryCoproductIso_hom_labelAppendSplit]
  change iter (fun current : LabelDen [A,B] =>
    collect (ε := ε) s (env, labelDenToFinite (localTypes A B) current) >>= fun target =>
      pure (LabelValue.appendSplit [A,B] (D :: extra) target)) (injectLocal (.inl env.2)) = _
  let raw : LabelDen [A,B] → m (LabelDen (D :: extra) ⊕ LabelDen [A,B]) := fun current =>
    collect (ε := ε) s (env, labelDenToFinite (localTypes A B) current) >>= fun target =>
      pure (LabelValue.appendSplit [A,B] (D :: extra) target)
  have comm : (mapReturn (flat (ε := ε) s) (pure ∘ externalExit) >=> liftPure (Sum.map id injectLocal)) =
      (liftPure injectLocal >=> raw) := by
    funext x
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, mapReturn, raw, bind_assoc]
    cases x with
    | inl a =>
      have h : labelDenToFinite (localTypes A B) (injectLocal (.inl a)) = ⟨0, a⟩ :=
        labelDenToFinite_recursiveInject (localTypes A B) 0 rfl a
      rw [h]
      simp only [flat, flattenBody, grouped, collect, actions, Fin.cases_zero,
        dispatchOuter, Bind.kleisliRight, liftPure, Function.comp_apply, bind_assoc, pure_bind]
      simp [Silmaril.Elgot.flatten, injectLocal, innerTarget, LabelValue.appendSplit]
    | inr b =>
      have h : labelDenToFinite (localTypes A B) (injectLocal (.inr b)) = ⟨1, b⟩ :=
        labelDenToFinite_recursiveInject (localTypes A B) 1 rfl b
      rw [h]
      change (flat (ε := ε) s (.inr b) >>= _) =
        dispatchInner (ε := ε) s b >>= fun target => pure (LabelValue.appendSplit [A,B] (D :: extra) target)
      simp only [flat, flattenBody, grouped, dispatchInner, Bind.kleisliRight, liftPure,
        Function.comp_apply, bind_assoc]
      congr 1
      funext result
      cases result with
      | inl k =>
        simp only [bind_assoc]
        congr 1
        funext result
        cases result <;> simp [Silmaril.Elgot.flatten, injectLocal, outerTarget, exitTarget, LabelValue.appendSplit]
      | inr next =>
        simp [Silmaril.Elgot.flatten, injectLocal, innerTarget, LabelValue.appendSplit]
  exact (by simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using
    (congrFun (LawfulElgotMonad.uniformity _ _ _ comm) (.inl env.2)).symm)

theorem region_round_withTail
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTypingWithTail s extra) env =
      iter (round (ε := ε) s) env.2 >>= fun d => pure (Sum.inl d) := by
  rw [denote_flat (ε := ε) s coherent env, ← LawfulElgotMonad.naturality]
  change iter (flat (ε := ε) s) (.inl env.2) >>= _ = _
  rw [flat, iterate_grouped]
  rfl

theorem region_round
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTyping s) env =
      iter (round (ε := ε) s) env.2 >>= fun d => pure (Sum.inl d) :=
  region_round_withTail s coherent env

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Proofs
