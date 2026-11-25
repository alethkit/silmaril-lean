module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Iteration

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Proofs

open CategoryTheory Silmaril.Elgot
open Isotope.LambdaSSA (Region)
open Isotope.SSA (At)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open TwoBlock.TwoExit (callCase)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B C D X Y : τ} {tail Γ L : List τ}

set_option backward.isDefEq.respectTransparency false

private def siteValue (target : Site L X) : TyDen X → LabelDen L :=
  LabelValue.inject target.index target.typing

omit [Iterate m] [LawfulElgotMonad m] in
private theorem call_denotes (op : TwoBlock.Instruction Φ X Y) (Γ : List τ) :
    Denotes (m := m) ε (op.typing Γ) (fun env => TwoBlock.call (ε := ε) op env.2) := by
  obtain ⟨op, source, target⟩ := op
  subst X
  subst Y
  have d := Denotes.op (m := m) (ε := ε)
    (Denotes.var (Φ := Φ) (Γ := instrSrc op :: Γ) (i := 0) rfl)
  simpa [TwoBlock.call, Env.get, bind_pure] using d

omit [LawfulElgotMonad m] in
private theorem branch_denotes (target : Site L X) :
    RegionDenotes (m := m) ε (.br target.typing (.var (Φ := Φ) (Γ := X :: Γ) (i := 0) rfl))
      (fun env => pure (siteValue target env.2)) := by
  simpa only [siteValue, Env.get, pure_bind, labelInject_eq_recursive] using
    RegionDenotes.br (m := m) (ε := ε) (h := target.typing)
      (Denotes.var (Φ := Φ) (Γ := X :: Γ) (i := 0) rfl)

omit [LawfulElgotMonad m] in
private theorem case_denotes (op : TwoBlock.Instruction Φ A (Silmaril.coprod X Y))
    (left : Site L X) (right : Site L Y) :
    RegionDenotes (m := m) ε
      (.case (op.typing Γ) (.br left.typing (.var (i := 0) rfl)) (.br right.typing (.var (i := 0) rfl)))
      (fun env => callCase (ε := ε) op env.2 >>= fun out =>
        pure (Sum.elim (siteValue left) (siteValue right) out)) := by
  have d := RegionDenotes.case (call_denotes (m := m) (ε := ε) op Γ)
    (branch_denotes (m := m) (ε := ε) (Φ := Φ) (Γ := A :: Γ) left)
    (branch_denotes (m := m) (ε := ε) (Φ := Φ) (Γ := A :: Γ) right)
  convert d using 1
  funext env
  simp only [callCase, bind_assoc, pure_bind]
  congr 1
  funext out
  cases TypeModel.coprodEquiv X Y out <;> rfl

private def bodyActions (back : Site L A) (exit : Site L D) :
    {B : τ} → {tail : List τ} → Body Φ A D B tail → Sites L (B :: tail) →
    ∀ i : Fin (B :: tail).length, Env ((B :: tail).get i :: Γ) → m (LabelDen L)
  | _, _, .last op, _, i =>
    Fin.cases (motive := fun j => Env ([_].get j :: Γ) → m (LabelDen L))
      (fun env => callCase (ε := ε) op env.2 >>= fun out => pure (Sum.elim (siteValue exit) (siteValue back) out))
      (fun j => j.elim0) i
  | _, _, .next op rest, sites, i =>
    Fin.cases (motive := fun j => Env ((_ :: _ :: _).get j :: Γ) → m (LabelDen L))
      (fun env => TwoBlock.call (ε := ε) op env.2 >>= fun x => pure (siteValue (sites (0 : Fin _).succ) x))
      (bodyActions back exit rest (fun j => sites j.succ)) i

omit [LawfulElgotMonad m] in
private theorem body_denotes (back : Site L A) (exit : Site L D) (body : Body Φ A D B tail)
    (sites : Sites L (B :: tail)) (i : Fin (B :: tail).length) :
    RegionDenotes (m := m) ε (body.blockTyping (Γ := Γ) sites back exit i)
      (bodyActions (ε := ε) back exit body sites i) := by
  induction body with
  | last op =>
    refine Fin.cases ?_ (fun j => j.elim0) i
    exact case_denotes op exit back
  | @next B X xs op rest ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · let target := sites (0 : Fin (X :: xs).length).succ
      have den := RegionDenotes.br (m := m) (ε := ε) (h := target.typing) (call_denotes (m := m) (ε := ε) op Γ)
      simp only [labelInject_eq_recursive] at den
      exact den
    · exact ih (fun j => sites j.succ) j

private def labelAt {n : Nat} (R : Fin n → τ) (i : Fin n) (x : TyDen (R i)) : LabelDen (List.ofFn R) :=
  LabelValue.inject i.val (by simp [At]) x

private theorem dispatch_at {n : Nat} (R : Fin n → τ) (i : Fin n) (x : TyDen (R i)) :
    labelDenToFinite R (labelAt R i x) = finiteLabelInject R i x :=
  labelDenToFinite_recursiveInject _ _ _ _

private theorem split_local (external : List τ) :
    (locals : List τ) → (i : Nat) → {X : τ} →
    (outside : At (locals ++ external) i X) → (inside : At locals i X) → (x : TyDen X) →
    LabelValue.appendSplit locals external (LabelValue.inject i outside x) =
      .inr (LabelValue.inject i inside x)
  | [], _, _, _, inside, _ => by simp [At] at inside
  | _ :: _, 0, _, _, _, _ => rfl
  | t :: rest, i + 1, X, outside, inside, x => by
    have h₁ : At (rest ++ external) i X := outside
    have h₀ : At rest i X := inside
    rw [LabelValue.inject_succ i outside h₁, LabelValue.inject_succ i inside h₀,
      LabelValue.appendSplit, split_local external rest i h₁ h₀ x]

private theorem split_external (external : List τ) :
    (locals : List τ) → (i : Nat) → {X : τ} →
    (outside : At (locals ++ external) (i + locals.length) X) →
    (inside : At external i X) → (x : TyDen X) →
    LabelValue.appendSplit locals external (LabelValue.inject (i + locals.length) outside x) =
      .inl (LabelValue.inject i inside x)
  | [], _, _, _, _, _ => rfl
  | t :: rest, i, X, outside, inside, x => by
    have ht : At (rest ++ external) (i + rest.length) X := outside
    have h : LabelValue.inject (i + (t :: rest).length) outside x =
        Sum.inr (LabelValue.inject (i + rest.length) ht x) :=
      LabelValue.inject_succ (i + rest.length) outside ht x
    rw [h, LabelValue.appendSplit, split_external external rest i ht inside x]

private theorem local_split {n : Nat} (R : Fin n → τ) (external : List τ) (i : Fin n) (x : TyDen (R i)) :
    LabelValue.appendSplit (List.ofFn R) external (siteValue (localSite R external i) x) =
      .inr (labelAt R i x) :=
  split_local external (List.ofFn R) i.val _ _ x

private theorem external_split {n : Nat} (R : Fin n → τ) (external : List τ) (i : Fin external.length)
    (x : TyDen (external.get i)) :
    LabelValue.appendSplit (List.ofFn R) external (siteValue (externalSite R external i) x) =
      .inl (LabelValue.inject i.val (List.getElem?_eq_getElem i.isLt) x) :=
  split_external external (List.ofFn R) i.val _ _ x

omit [Iterate m] [LawfulElgotMonad m] in
private theorem body_split {I E : Type u} (split : LabelDen L → E ⊕ I)
    (back : Site L A) (exit : Site L D) (resume : TyDen A → I) (leave : TyDen D → E)
    (backSplit : ∀ a, split (siteValue back a) = .inr (resume a))
    (exitSplit : ∀ d, split (siteValue exit d) = .inl (leave d))
    (body : Body Φ A D B tail) (sites : Sites L (B :: tail))
    (locate : ∀ i : Fin (B :: tail).length, TyDen ((B :: tail).get i) → I)
    (siteSplit : ∀ i x, split (siteValue (sites i) x) = .inr (locate i x))
    (i : Fin (B :: tail).length) (env : Env ((B :: tail).get i :: Γ)) :
    (bodyActions (ε := ε) (m := m) back exit body sites i env >>= fun l => pure (split l)) =
      (innerBody (ε := ε) resume leave body locate i env.2 >>= fun s => pure (flatten s)) := by
  induction body with
  | last op =>
    revert env
    refine Fin.cases ?_ (fun j => j.elim0) i
    intro env
    simp only [bodyActions, innerBody, Fin.cases_zero, bind_assoc, pure_bind]
    congr 1
    funext r
    cases r with
    | inl d => exact congrArg pure (exitSplit d)
    | inr a => exact congrArg pure (backSplit a)
  | next op rest ih =>
    revert env
    refine Fin.cases ?_ (fun j => ?_) i
    · intro env
      simp only [bodyActions, innerBody, Fin.cases_zero, bind_assoc, pure_bind]
      congr 1
      funext x
      exact congrArg pure (siteSplit (0 : Fin _).succ x)
    · intro env
      simp only [bodyActions, innerBody, Fin.cases_succ]
      exact ih (fun i => sites i.succ) (fun i => locate i.succ)
        (fun i x => siteSplit i.succ x) j env

theorem region_denotes (s : Blocks Φ A B C D tail) :
    RegionDenotes (m := m) ε (regionTyping s) (regionAction (ε := ε) s) := by
  let R := localTypes A B tail
  let loc := List.ofFn R
  let out := [C,D]
  let back := localSite R out 0
  let left := externalSite R out 0
  let right := externalSite R out 1
  let next := localSite R out (0 : Fin (B :: tail).length).succ
  let sites := bodySites A B C D tail
  let entry : Env [A] → m (LabelDen (loc ++ out)) := fun env => pure (siteValue back env.2)
  let actions (i : Fin (A :: B :: tail).length) : Env (R i :: [A]) → m (LabelDen (loc ++ out)) :=
    Fin.cases (motive := fun j => Env (R j :: [A]) → m (LabelDen (loc ++ out)))
      (fun env => callCase (ε := ε) s.header env.2 >>= fun r =>
        pure (Sum.elim (siteValue left) (siteValue next) r))
      (bodyActions (ε := ε) back right s.body sites) i
  have blocks (i : Fin (A :: B :: tail).length) :
      RegionDenotes (m := m) ε (blockTyping s i) (actions i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact case_denotes s.header left next
    · exact body_denotes back right s.body sites j
  let collective : Env [A] × FiniteLabelDen R → m (LabelDen (loc ++ out)) :=
    fun p => actions p.2.1 (p.1, p.2.2)
  have agrees : CollectiveDenotes [A] R out actions collective := ⟨fun _ _ _ => rfl⟩
  have den := RegionDenotes.cfg _ _ (branch_denotes (Γ := []) back) blocks agrees
  have eq : cfgDenotation (R := R) entry collective = regionAction (ε := ε) s := by
    funext env
    let resume : TyDen A → LabelDen loc := labelAt R 0
    let enterBody : ∀ i : Fin (B :: tail).length, TyDen ((B :: tail).get i) → LabelDen loc :=
      fun i => labelAt R i.succ
    let leave : TyDen D → LabelDen out := fun d => .inr (.inl d)
    let split := LabelValue.appendSplit loc out
    let dispatch (p : FiniteLabelDen R) : m ((LabelDen out ⊕ LabelDen loc) ⊕ LabelDen loc) :=
      Fin.cases (motive := fun j => TyDen (R j) → m ((LabelDen out ⊕ LabelDen loc) ⊕ LabelDen loc))
        (fun a => callCase (ε := ε) s.header a >>= fun
          | .inl c => pure (.inl (.inl (.inl c)))
          | .inr b => pure (.inr (enterBody 0 b)))
        (innerBody (ε := ε) resume leave s.body enterBody) p.1 p.2
    let inner : LabelDen loc → m ((LabelDen out ⊕ LabelDen loc) ⊕ LabelDen loc) :=
      fun l => dispatch (labelDenToFinite R l)
    have hBack (a : TyDen A) : split (siteValue back a) = .inr (resume a) := local_split R out 0 a
    have hLeft (c : TyDen C) : split (siteValue left c) = .inl (.inl c) := external_split R out 0 c
    have hRight (d : TyDen D) : split (siteValue right d) = .inl (leave d) := external_split R out 1 d
    have hSites (i) (x) : split (siteValue (sites i) x) = .inr (enterBody i x) := local_split R out i.succ x
    have flat : (fun l => collective (env, labelDenToFinite R l) >>= fun next => pure (split next)) =
        flattenBody inner := by
      funext l
      unfold flattenBody Bind.kleisliRight liftPure inner
      obtain ⟨i, a⟩ := labelDenToFinite R l
      revert a
      refine Fin.cases ?_ (fun j => ?_) i
      · intro a
        simp only [collective, actions, dispatch, Fin.cases_zero, bind_assoc, pure_bind]
        congr 1
        funext r
        cases r with
        | inl c =>
          simp only [Sum.elim_inl, pure_bind, Function.comp_apply, flatten, id_eq]
          exact congrArg (pure : LabelDen out ⊕ LabelDen loc → m _) (hLeft c)
        | inr b =>
          simp only [Sum.elim_inr, pure_bind, Function.comp_apply, flatten]
          exact congrArg (pure : LabelDen out ⊕ LabelDen loc → m _) (hSites 0 b)
      · intro x
        simp only [collective, actions, dispatch, Fin.cases_succ]
        exact body_split split back right resume leave hBack hRight s.body sites enterBody hSites j (env, x)
    have atBody (b : TyDen B) :
        iter inner (enterBody 0 b) = s.body.fold (ε := ε) b >>= fun r => pure (Sum.map leave resume r) := by
      apply iter_body resume leave s.body enterBody inner _ b
      intro i x
      unfold inner enterBody
      rw [dispatch_at]
      rfl
    have atHeader (a : TyDen A) :
        iter inner (resume a) = round (ε := ε) s a >>= fun r => pure (Sum.map id resume r) := by
      let atHead : TyDen A → m ((LabelDen out ⊕ LabelDen loc) ⊕ LabelDen loc) := fun a =>
        callCase (ε := ε) s.header a >>= fun
          | .inl c => pure (.inl (.inl (.inl c)))
          | .inr b => pure (.inr (enterBody 0 b))
      have one : inner (resume a) = atHead a := by
        unfold inner resume
        rw [dispatch_at]
        rfl
      rw [congrFun (LawfulElgotMonad.fixpoint inner) (resume a), one]
      simp only [atHead, round, bind_assoc]
      congr 1
      funext r
      cases r with
      | inl c => simp only [pure_bind]; rfl
      | inr b =>
        simp only [pure_bind, Sum.elim_inr]
        rw [atBody b, bind_assoc]
        congr 1
        funext out
        cases out <;> simp only [pure_bind] <;> rfl
    simp only [cfgDenotation, entry, pure_bind, binaryCoproductIso_hom_labelAppendSplit]
    have initial : LabelValue.appendSplit (List.ofFn R) out (siteValue back env.2) =
        .inr (resume env.2) := hBack env.2
    rw [initial]
    change iter (fun x => collective (env, labelDenToFinite R x) >>= fun next => pure (split next))
      (resume env.2) = _
    rw [flat]
    exact close_grouped resume inner (round (ε := ε) s) atHeader env.2
  change RegionDenotes (m := m) ε (regionTyping s) (cfgDenotation (R := R) entry collective) at den
  rwa [eq] at den

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Proofs
