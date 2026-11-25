module

public import Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.ThreeBlock.Iteration
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Proofs

open CategoryTheory Silmaril.Elgot
open Isotope.LambdaSSA (Tm Region)
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics
open TwoBlock.TwoExit (callCase exitLabel)

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

private def headerTarget : TyDen C ⊕ TyDen B → LabelDen [A, B, X, C, D]
  | .inl c => .inr (.inr (.inr (.inl c)))
  | .inr b => .inr (.inl b)

private def lastTarget : TyDen D ⊕ TyDen A → LabelDen [A, B, X, C, D]
  | .inl d => .inr (.inr (.inr (.inr (.inl d))))
  | .inr a => .inl a

omit [LawfulElgotMonad m] in
private theorem headerDenotes (s : Blocks Φ A B X C D) :
    RegionDenotes (m := m) ε (headerTyping s)
      (fun env => callCase (ε := ε) s.header env.2 >>= fun result => pure (headerTarget result)) := by
  have dl := branch (m := m) (ε := ε) (Φ := Φ) (Γ := [A,A])
    (show Isotope.SSA.At [A,B,X,C,D] 3 C from rfl)
  have dr := branch (m := m) (ε := ε) (Φ := Φ) (Γ := [A,A])
    (show Isotope.SSA.At [A,B,X,C,D] 1 B from rfl)
  have d := RegionDenotes.case (callDenotes s.header [A]) dl dr
  convert d using 1
  · rfl
  · funext env
    simp only [callCase, bind_assoc, pure_bind]
    congr 1
    funext payload
    cases TypeModel.coprodEquiv C B payload <;> rfl

omit [LawfulElgotMonad m] in
private theorem firstDenotes (s : Blocks Φ A B X C D) :
    RegionDenotes (m := m) ε (firstTyping s)
      (fun env => TwoBlock.call (ε := ε) s.first env.2 >>= fun x => pure (.inr (.inr (.inl x)))) := by
  simpa only [labelInject_eq_recursive, LabelValue.inject] using
    RegionDenotes.br (m := m) (ε := ε) (h := (show Isotope.SSA.At [A,B,X,C,D] 2 X from rfl))
      (callDenotes s.first [A])

omit [LawfulElgotMonad m] in
private theorem lastDenotes (s : Blocks Φ A B X C D) :
    RegionDenotes (m := m) ε (lastTyping s)
      (fun env => callCase (ε := ε) s.last env.2 >>= fun result => pure (lastTarget result)) := by
  have dl := branch (m := m) (ε := ε) (Φ := Φ) (Γ := [X,A])
    (show Isotope.SSA.At [A,B,X,C,D] 4 D from rfl)
  have dr := branch (m := m) (ε := ε) (Φ := Φ) (Γ := [X,A])
    (show Isotope.SSA.At [A,B,X,C,D] 0 A from rfl)
  have d := RegionDenotes.case (callDenotes s.last [A]) dl dr
  convert d using 1
  · rfl
  · funext env
    simp only [callCase, bind_assoc, pure_bind]
    congr 1
    funext payload
    cases TypeModel.coprodEquiv D A payload <;> rfl

private def internal : TyDen A ⊕ (TyDen B ⊕ TyDen X) → LabelDen [A, B, X]
  | .inl a => .inl a
  | .inr (.inl b) => .inr (.inl b)
  | .inr (.inr x) => .inr (.inr (.inl x))

theorem region_iterates (s : Blocks Φ A B X C D) :
    RegionDenotes (m := m) ε (regionTyping s) (regionAction (ε := ε) s) := by
  let R := localTypes A B X
  let entry : Env [A] → m (LabelDen [A,B,X,C,D]) := fun env => pure (Sum.inl env.2)
  have entryDen : RegionDenotes (m := m) ε
      (.br (L := [A,B,X,C,D]) (ℓ := 0) rfl (.var (Φ := Φ) (Γ := [A]) (i := 0) rfl)) entry :=
    branch (m := m) (ε := ε) (Φ := Φ) (Γ := []) (show Isotope.SSA.At [A,B,X,C,D] 0 A from rfl)
  let actions (i : Fin 3) : Env (R i :: [A]) → m (LabelDen [A,B,X,C,D]) :=
    Fin.cases (motive := fun j => Env (R j :: [A]) → m (LabelDen [A,B,X,C,D]))
      (fun env => callCase (ε := ε) s.header env.2 >>= fun r => pure (headerTarget r))
      (Fin.cases (motive := fun j => Env (R j.succ :: [A]) → m (LabelDen [A,B,X,C,D]))
        (fun env => TwoBlock.call (ε := ε) s.first env.2 >>= fun x => pure (.inr (.inr (.inl x))))
        (fun _ env => callCase (ε := ε) s.last env.2 >>= fun r => pure (lastTarget r))) i
  have blocks (i : Fin 3) : RegionDenotes (m := m) ε (blockTyping s i) (actions i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact headerDenotes s
    · refine Fin.cases ?_ (fun _ => ?_) j
      · exact firstDenotes s
      · exact lastDenotes s
  let dispatcher : Env [A] × FiniteLabelDen R → m (LabelDen [A,B,X,C,D]) :=
    fun pair => actions pair.2.1 (pair.1, pair.2.2)
  have collective : CollectiveDenotes [A] R [C,D] actions dispatcher := ⟨fun _ _ _ => rfl⟩
  have den := RegionDenotes.cfg _ _ entryDen blocks collective
  have eq : cfgDenotation (R := R) entry dispatcher = regionAction (ε := ε) s := by
    funext env
    let g : LabelDen [A,B,X] → m (LabelDen [C,D] ⊕ LabelDen [A,B,X]) := fun current =>
      dispatcher (env, labelDenToFinite R current) >>= fun next =>
        pure (LabelValue.appendSplit [A,B,X] [C,D] next)
    let h : TyDen A → m ((TyDen C ⊕ TyDen D) ⊕ TyDen B) :=
      fun a => callCase (ε := ε) s.header a >>= fun r => pure (Sum.map Sum.inl id r)
    let p : TyDen B → m (TyDen X) := TwoBlock.call (ε := ε) s.first
    let q : TyDen X → m ((TyDen C ⊕ TyDen D) ⊕ TyDen A) :=
      fun x => callCase (ε := ε) s.last x >>= fun r => pure (Sum.map Sum.inr id r)
    let f := dispatch h p q
    have steps (current : TyDen A ⊕ (TyDen B ⊕ TyDen X)) :
        g (internal current) = f current >>= fun result => pure (Sum.map exitLabel internal result) := by
      rcases current with a | b | x
      · have route : labelDenToFinite R (internal (.inl a)) = finiteLabelInject R 0 a :=
          labelDenToFinite_recursiveInject R 0 rfl a
        unfold g
        rw [route]
        simp only [dispatcher, finiteLabelInject, actions, Fin.cases_zero, f, dispatch, h, bind_assoc, pure_bind]
        congr 1
        funext result
        cases result <;> rfl
      · have route : labelDenToFinite R (internal (.inr (.inl b))) = finiteLabelInject R ((0 : Fin 2).succ) b :=
          labelDenToFinite_recursiveInject R ((0 : Fin 2).succ) rfl b
        unfold g
        rw [route]
        simp only [dispatcher, finiteLabelInject, actions, Fin.cases_succ, Fin.cases_zero,
          f, dispatch, p, bind_assoc, pure_bind]
        rfl
      · let two := ((0 : Fin 1).succ).succ
        have route : labelDenToFinite R (internal (.inr (.inr x))) = finiteLabelInject R two x :=
          labelDenToFinite_recursiveInject R two rfl x
        unfold g
        rw [route]
        simp only [dispatcher, finiteLabelInject, actions, two, Fin.cases_succ, f, dispatch, q, bind_assoc, pure_bind]
        congr 1
        funext result
        cases result <;> rfl
    have initial : LabelValue.appendSplit (List.ofFn R) [C,D]
        (Sum.inl env.2 : LabelDen (List.ofFn R ++ [C,D])) = Sum.inr (internal (.inl env.2)) := rfl
    simp only [cfgDenotation, entry, pure_bind, binaryCoproductIso_hom_labelAppendSplit, initial]
    change iter g (internal (.inl env.2)) = _
    rw [OrderedTheta.iter_boundary f g internal exitLabel steps]
    have grouped := group_chain h p q (round (ε := ε) s) (fun a => by
      simp only [h, round, bind_assoc, pure_bind]
      congr 1
      funext result
      cases result <;> rfl) env.2
    change (iter (dispatch h p q) (.inl env.2) >>= _) = _
    rw [grouped]
    rfl
  rwa [eq] at den

end Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Proofs
