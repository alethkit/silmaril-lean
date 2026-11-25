module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Proofs

open CategoryTheory Silmaril.Elgot
open Isotope.LambdaSSA (Tm Region)
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B C D X Y : τ}

set_option backward.isDefEq.respectTransparency false

omit [Iterate m] [LawfulElgotMonad m] in
private theorem callDenotes (op : TwoBlock.Instruction Φ X Y) (Γ : List τ) :
    Denotes (m := m) ε (op.typing Γ) (fun env => TwoBlock.call (ε := ε) op env.2) := by
  obtain ⟨op, src, dst⟩ := op
  subst X
  subst Y
  have d := Denotes.op (m := m) (ε := ε)
    (Denotes.var (Φ := Φ) (Γ := instrSrc op :: Γ) (i := 0) rfl)
  simpa [TwoBlock.call, Env.get, bind_pure] using d

omit [LawfulElgotMonad m] in
private theorem branch {Γ L : List τ} {i : Nat} (l : Isotope.SSA.At L i X) :
    RegionDenotes (m := m) ε (.br l (.var (Φ := Φ) (Γ := X :: Γ) (i := 0) rfl))
      (fun env => pure (LabelValue.inject i l env.2)) := by
  simpa only [Env.get, pure_bind, labelInject_eq_recursive] using RegionDenotes.br (m := m) (ε := ε) (h := l)
    (Denotes.var (Φ := Φ) (Γ := X :: Γ) (i := 0) rfl)

private def headerTarget : TyDen C ⊕ TyDen B → LabelDen [A, B, C, D]
  | .inl c => .inr (.inr (.inl c))
  | .inr b => .inr (.inl b)

private def bodyTarget : TyDen D ⊕ TyDen A → LabelDen [A, B, C, D]
  | .inl d => .inr (.inr (.inr (.inl d)))
  | .inr a => .inl a

omit [LawfulElgotMonad m] in
private theorem headerDenotes (s : Blocks Φ A B C D) :
    RegionDenotes (m := m) ε (headerTyping s)
      (fun env => callCase (ε := ε) s.header env.2 >>= fun result => pure (headerTarget result)) := by
  have dl := branch (m := m) (ε := ε) (Φ := Φ) (Γ := [A,A])
    (show Isotope.SSA.At [A,B,C,D] 2 C from rfl)
  have dr := branch (m := m) (ε := ε) (Φ := Φ) (Γ := [A,A])
    (show Isotope.SSA.At [A,B,C,D] 1 B from rfl)
  have d := RegionDenotes.case (callDenotes s.header [A]) dl dr
  convert d using 1
  · rfl
  · funext env
    simp only [callCase, bind_assoc, pure_bind]
    congr 1
    funext payload
    cases TypeModel.coprodEquiv C B payload <;> rfl

omit [LawfulElgotMonad m] in
private theorem bodyDenotes (s : Blocks Φ A B C D) :
    RegionDenotes (m := m) ε (bodyTyping s)
      (fun env => callCase (ε := ε) s.body env.2 >>= fun result => pure (bodyTarget result)) := by
  have dl := branch (m := m) (ε := ε) (Φ := Φ) (Γ := [B,A])
    (show Isotope.SSA.At [A,B,C,D] 3 D from rfl)
  have dr := branch (m := m) (ε := ε) (Φ := Φ) (Γ := [B,A])
    (show Isotope.SSA.At [A,B,C,D] 0 A from rfl)
  have d := RegionDenotes.case (callDenotes s.body [A]) dl dr
  convert d using 1
  · rfl
  · funext env
    simp only [callCase, bind_assoc, pure_bind]
    congr 1
    funext payload
    cases TypeModel.coprodEquiv D A payload <;> rfl

private def internal : TyDen A ⊕ TyDen B → LabelDen [A, B]
  | .inl a => .inl a
  | .inr b => .inr (.inl b)

theorem region_iterates (s : Blocks Φ A B C D) :
    RegionDenotes (m := m) ε (regionTyping s)
      (fun env => iter (round (ε := ε) s) env.2 >>= fun out => pure (exitLabel out)) := by
  let R := TwoBlock.localTypes A B
  let entry : Env [A] → m (LabelDen [A,B,C,D]) := fun env => pure (Sum.inl env.2)
  have entryDen : RegionDenotes (m := m) ε
      (.br (L := [A,B,C,D]) (ℓ := 0) rfl (.var (Φ := Φ) (Γ := [A]) (i := 0) rfl)) entry :=
    branch (m := m) (ε := ε) (Φ := Φ) (Γ := []) (show Isotope.SSA.At [A,B,C,D] 0 A from rfl)
  let actions (i : Fin 2) : Env (R i :: [A]) → m (LabelDen [A,B,C,D]) :=
    Fin.cases (motive := fun j => Env (R j :: [A]) → m (LabelDen [A,B,C,D]))
      (fun env => callCase (ε := ε) s.header env.2 >>= fun r => pure (headerTarget r))
      (fun _ env => callCase (ε := ε) s.body env.2 >>= fun r => pure (bodyTarget r)) i
  have blocks (i : Fin 2) : RegionDenotes (m := m) ε (blockTyping s i) (actions i) := by
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact headerDenotes s
    · exact bodyDenotes s
  let dispatcher : Env [A] × FiniteLabelDen R → m (LabelDen [A,B,C,D]) :=
    fun pair => actions pair.2.1 (pair.1, pair.2.2)
  have collective : CollectiveDenotes [A] R [C,D] actions dispatcher := ⟨fun _ _ _ => rfl⟩
  have den := RegionDenotes.cfg _ _ entryDen blocks collective
  have eq : cfgDenotation (R := R) entry dispatcher =
      (fun env => iter (round (ε := ε) s) env.2 >>= fun out => pure (exitLabel out)) := by
    funext env
    let g : LabelDen [A,B] → m (LabelDen [C,D] ⊕ LabelDen [A,B]) := fun current =>
      dispatcher (env, labelDenToFinite R current) >>= fun next =>
        pure (LabelValue.appendSplit [A,B] [C,D] next)
    let h : TyDen A → m ((TyDen C ⊕ TyDen D) ⊕ TyDen B) :=
      fun a => callCase (ε := ε) s.header a >>= fun r => pure (Sum.map Sum.inl id r)
    let b : TyDen B → m ((TyDen C ⊕ TyDen D) ⊕ TyDen A) :=
      fun b => callCase (ε := ε) s.body b >>= fun r => pure (Sum.map Sum.inr id r)
    let f := TwoBlock.labelStepWithExits h b
    have steps (x : TyDen A ⊕ TyDen B) :
        g (internal x) = f x >>= fun result => pure (Sum.map exitLabel internal result) := by
      cases x with
      | inl a =>
        have route : labelDenToFinite R (internal (.inl a)) = finiteLabelInject R 0 a :=
          labelDenToFinite_recursiveInject R 0 rfl a
        unfold g
        rw [route]
        simp only [dispatcher, finiteLabelInject, actions, Fin.cases_zero, f, TwoBlock.labelStepWithExits, h, bind_assoc, pure_bind]
        congr 1
        funext result
        cases result <;> rfl
      | inr y =>
        have route : labelDenToFinite R (internal (.inr y)) = finiteLabelInject R ((0 : Fin 1).succ) y :=
          labelDenToFinite_recursiveInject R ((0 : Fin 1).succ) rfl y
        unfold g
        rw [route]
        simp only [dispatcher, finiteLabelInject, actions, Fin.cases_succ, f, TwoBlock.labelStepWithExits, b, bind_assoc, pure_bind]
        congr 1
        funext result
        cases result <;> rfl
    have initial : LabelValue.appendSplit (List.ofFn R) [C,D]
        (Sum.inl env.2 : LabelDen (List.ofFn R ++ [C,D])) = Sum.inr (internal (.inl env.2)) := rfl
    simp only [cfgDenotation, entry, pure_bind, binaryCoproductIso_hom_labelAppendSplit, initial]
    change iter g (internal (.inl env.2)) = _
    rw [OrderedTheta.iter_boundary f g internal exitLabel steps]
    have grouped := TwoBlock.group_labels h b env.2
    have advance : (fun a => h a >>= Sum.elim (pure ∘ Sum.inl) b) = round (ε := ε) s := by
      funext a
      simp only [h, round, bind_assoc, pure_bind]
      congr 1
      funext result
      cases result with
      | inl c => rfl
      | inr y =>
        simp only [Sum.map_inr, id_eq, Sum.elim_inr, b]
        congr 1
        funext result
        cases result <;> rfl
    rw [advance] at grouped
    change (iter (TwoBlock.labelStepWithExits h b) (.inl env.2) >>= _) = _
    rw [grouped]
  rw [eq] at den
  exact den

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Proofs
