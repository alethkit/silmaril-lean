module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.Iteration

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Proofs

open CategoryTheory Silmaril.Elgot
open Isotope.LambdaSSA (Tm Region)
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (exit)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B C : τ}

set_option backward.isDefEq.respectTransparency false

omit [Iterate m] [LawfulElgotMonad m] in
private theorem callDenotes (op : Instruction Φ A C) (Γ : List τ) :
    Denotes (m := m) ε (op.typing Γ) (fun env => call (ε := ε) op env.2) := by
  obtain ⟨op, src, dst⟩ := op
  subst A
  subst C
  have d := Denotes.op (m := m) (ε := ε)
    (Denotes.var (Φ := Φ) (Γ := instrSrc op :: Γ) (i := 0) rfl)
  simpa [call, Env.get, bind_pure] using d

private def headerTarget : TyDen A ⊕ TyDen B → LabelDen [A, B, A]
  | .inl a => .inr (.inr (exit a))
  | .inr b => .inr (.inl b)

omit [LawfulElgotMonad m] in
private theorem headerDenotes (s : Blocks Φ A B) :
    RegionDenotes (m := m) ε (headerTyping s)
      (fun env => headerAction (ε := ε) s.header env.2 >>= fun result => pure (headerTarget result)) := by
  have dl : RegionDenotes (m := m) ε
      (.br (L := [A, B, A]) (ℓ := 2) rfl (.var (Φ := Φ) (Γ := [A, A, A]) (i := 0) rfl))
      (fun env => pure (.inr (.inr (exit env.2)))) := by
    have d := RegionDenotes.br (m := m) (ε := ε) (h := (show Isotope.SSA.At [A,B,A] 2 A from rfl))
      (Denotes.var (Φ := Φ) (Γ := [A,A,A]) (i := 0) rfl)
    simpa [Env.get, exit, LabelValue.inject] using d
  have dr : RegionDenotes (m := m) ε
      (.br (L := [A, B, A]) (ℓ := 1) rfl (.var (Φ := Φ) (Γ := [B, A, A]) (i := 0) rfl))
      (fun env => pure (.inr (.inl env.2))) := by
    have d := RegionDenotes.br (m := m) (ε := ε) (h := (show Isotope.SSA.At [A,B,A] 1 B from rfl))
      (Denotes.var (Φ := Φ) (Γ := [B,A,A]) (i := 0) rfl)
    simpa [Env.get, LabelValue.inject] using d
  have d := RegionDenotes.case (callDenotes s.header [A]) dl dr
  convert d using 1
  · rfl
  · funext env
    simp only [headerAction, bind_assoc, pure_bind]
    congr 1
    funext payload
    cases TypeModel.coprodEquiv A B payload <;> rfl

omit [LawfulElgotMonad m] in
private theorem bodyDenotes (s : Blocks Φ A B) :
    RegionDenotes (m := m) ε (bodyTyping s)
      (fun env => call (ε := ε) s.body env.2 >>= fun result => pure (Sum.inl result)) := by
  have d := RegionDenotes.br (m := m) (ε := ε) (h := (show Isotope.SSA.At [A,B,A] 0 A from rfl))
    (callDenotes s.body [A])
  simpa [LabelValue.inject] using d

private def internal : TyDen A ⊕ TyDen B → LabelDen [A, B]
  | .inl a => .inl a
  | .inr b => .inr (.inl b)

theorem region_iterates (s : Blocks Φ A B) :
    RegionDenotes (m := m) ε (regionTyping s)
      (fun env => iter (round (ε := ε) s) env.2 >>= fun a => pure (exit a)) := by
  let R := localTypes A B
  let entry : Env [A] → m (LabelDen [A,B,A]) := fun env => pure (Sum.inl env.2)
  have entryDen : RegionDenotes (m := m) ε
      (.br (L := [A,B,A]) (ℓ := 0) rfl (.var (Φ := Φ) (Γ := [A]) (i := 0) rfl)) entry := by
    have d := RegionDenotes.br (m := m) (ε := ε) (h := (show Isotope.SSA.At [A,B,A] 0 A from rfl))
      (Denotes.var (Φ := Φ) (Γ := [A]) (i := 0) rfl)
    simpa [Env.get, entry, LabelValue.inject] using d
  let actions (i : Fin 2) : Env (R i :: [A]) → m (LabelDen [A,B,A]) :=
    Fin.cases (motive := fun j => Env (R j :: [A]) → m (LabelDen [A,B,A]))
      (fun env => headerAction (ε := ε) s.header env.2 >>= fun r => pure (headerTarget r))
      (fun _ env => call (ε := ε) s.body env.2 >>= fun a => pure (Sum.inl a)) i
  have blocks (i : Fin 2) : RegionDenotes (m := m) ε (blockTyping s i) (actions i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact headerDenotes s
    · exact bodyDenotes s
  let dispatcher : Env [A] × FiniteLabelDen R → m (LabelDen [A,B,A]) :=
    fun pair => actions pair.2.1 (pair.1, pair.2.2)
  have collective : CollectiveDenotes [A] R [A] actions dispatcher := ⟨fun _ _ _ => rfl⟩
  have den := RegionDenotes.cfg _ _ entryDen blocks collective
  have eq : cfgDenotation (R := R) entry dispatcher =
      (fun env => iter (round (ε := ε) s) env.2 >>= fun a => pure (exit a)) := by
    funext env
    let g : LabelDen [A,B] → m (LabelDen [A] ⊕ LabelDen [A,B]) := fun current =>
      dispatcher (env, labelDenToFinite R current) >>= fun next =>
        pure (LabelValue.appendSplit [A,B] [A] next)
    let f : TyDen A ⊕ TyDen B → m (TyDen A ⊕ (TyDen A ⊕ TyDen B)) :=
      labelStep (headerAction (m := m) (ε := ε) s.header) (call (ε := ε) s.body)
    have steps (x : TyDen A ⊕ TyDen B) :
        g (internal x) = f x >>= fun result => pure (Sum.map exit internal result) := by
      cases x with
      | inl a =>
        have route : labelDenToFinite R (internal (.inl a)) = finiteLabelInject R 0 a :=
          labelDenToFinite_recursiveInject R 0 rfl a
        unfold g
        rw [route]
        simp only [dispatcher, finiteLabelInject, actions, Fin.cases_zero, f, labelStep, bind_assoc, pure_bind]
        congr 1
        funext result
        cases result <;> rfl
      | inr b =>
        have route : labelDenToFinite R (internal (.inr b)) = finiteLabelInject R ((0 : Fin 1).succ) b :=
          labelDenToFinite_recursiveInject R ((0 : Fin 1).succ) rfl b
        unfold g
        rw [route]
        simp only [dispatcher, finiteLabelInject, actions, Fin.cases_succ, f, labelStep, bind_assoc, pure_bind]
        rfl
    have initial : LabelValue.appendSplit (List.ofFn R) [A]
        (Sum.inl env.2 : LabelDen (List.ofFn R ++ [A])) = Sum.inr (internal (.inl env.2)) := rfl
    simp only [cfgDenotation, entry, pure_bind, binaryCoproductIso_hom_labelAppendSplit, initial]
    change iter g (internal (.inl env.2)) = _
    rw [OrderedTheta.iter_boundary f g internal exit steps]
    have grouped := collapse (headerAction (ε := ε) (m := m) s.header) (call (ε := ε) (m := m) s.body)
      (round (ε := ε) (m := m) s) (fun _ => by
        unfold round
        congr 1
        funext result
        cases result <;> rfl) env.2
    exact congrArg (fun (result : m (TyDen A)) => result >>= fun a => pure (exit a)) grouped
  rw [eq] at den
  exact den

open Isotope.LambdaSSA.Semantics.Agreement
open Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Isotope.LambdaSSA.Semantics.Categorical (ofMonadicTypeModel ofMonadicInstructionModel)

/-- Identify the structural result with the chosen SSA denotation using
coherence of the induced Kleisli model. -/
theorem chosen_eq (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {r : Region Φ} {h : Region.HasType [A] r [A]} {f : Env [A] → m (LabelDen [A])}
    (d : RegionDenotes (m := m) ε h f) : Region.denote (ε := ε) (m := m) h = f := by
  let _ := ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  let J := typeJ (m := m)
  let T := ofMonadicTypeModel (τ := τ)
  let _ : Isotope.LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := Φ) J T := coherent
  obtain ⟨F, dF, hF⟩ := regionDenotes_toCategorical (Region.denote_spec (ε := ε) (m := m) h)
  obtain ⟨G, dG, hG⟩ := regionDenotes_toCategorical d
  have eq := Isotope.LambdaSSA.Semantics.Categorical.RegionTypingCoherent.denotes_eq (J := J) (M := T) dF dG
  funext env
  have encoded := (congrFun hF env).symm.trans
    ((congrArg (fun F => F.of (envToCategorical env)) eq).trans (congrFun hG env))
  let decode := fun x => (pure ((LabelValue.categoricalEquiv [A]).symm x) : m (LabelDen [A]))
  simpa only [decode, bind_assoc, pure_bind, Equiv.symm_apply_apply, bind_pure] using
    congrArg (fun result => result >>= decode) encoded

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Proofs
