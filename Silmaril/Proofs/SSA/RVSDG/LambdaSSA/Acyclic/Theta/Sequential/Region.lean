module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Iteration

/-! # Direct monadic denotation of the flat two-loop CFG -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Proofs

open Isotope.LambdaSSA (Region)
open Isotope.SSA (At)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open LinearChain (Site localSite externalSite)
open TwoBlock.TwoExit (callCase)
open Silmaril.Elgot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B K M C J E D X Y : τ} {L Γ : List τ}

private def siteValue (target : Site L X) : TyDen X → LabelDen L :=
  LabelValue.inject target.index target.typing

omit [Iterate m] [LawfulElgotMonad m] in
private theorem call_denotes (op : TwoBlock.Instruction Φ X Y) :
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

/-- The denotation of a generated block only uses its current payload.
The routing function determines the result of its actual branch. -/
private def blockAction {O : Type u} (route : ∀ {Z}, Site L Z → TyDen Z → O) :
    Block Φ L X → TyDen X → m O
  | .jump op site, x => TwoBlock.call (ε := ε) op x >>= fun y => pure (route site y)
  | .branch op left right, x => callCase (ε := ε) op x >>= fun y =>
      pure (Sum.elim (route left) (route right) y)

omit [LawfulElgotMonad m] in
private theorem block_denotes (block : Block Φ L X) :
    RegionDenotes (m := m) ε (block.typing Γ) (fun env =>
      blockAction (ε := ε) siteValue block env.2) := by
  cases block with
  | jump op site =>
    simpa only [Block.typing, blockAction, labelInject_eq_recursive, siteValue] using
      RegionDenotes.br (m := m) (ε := ε) (h := site.typing) (call_denotes op)
  | branch op l r =>
    have den := RegionDenotes.case (call_denotes (Γ := Γ) op)
      (branch_denotes (m := m) (ε := ε) (Φ := Φ) (Γ := X :: Γ) l)
      (branch_denotes (m := m) (ε := ε) (Φ := Φ) (Γ := X :: Γ) r)
    change RegionDenotes (m := m) ε
      (.case (op.typing Γ) (.br l.typing (.var (i := 0) rfl)) (.br r.typing (.var (i := 0) rfl))) _
    convert den using 1
    funext env
    simp only [blockAction, callCase, bind_assoc, pure_bind]
    congr 1
    funext out
    cases TypeModel.coprodEquiv _ _ out <;> rfl

omit [Iterate m] [LawfulElgotMonad m] in
private theorem block_map {I O : Type u} {R : List τ}
    (block : Block Φ L X) (x : TyDen X) (rename : ∀ {Z}, Site L Z → Site R Z)
    (src : ∀ {Z}, Site L Z → TyDen Z → I) (dest : ∀ {Z}, Site R Z → TyDen Z → O)
    (map : I → O) (commute : ∀ {Z} (site : Site L Z) (p : TyDen Z),
      dest (rename site) p = map (src site p)) :
    blockAction (ε := ε) (m := m) dest (block.rename rename) x =
      blockAction (ε := ε) src block x >>= fun r => pure (map r) := by
  cases block with
  | jump op site =>
    simp only [Block.rename, blockAction, bind_assoc, pure_bind, commute]
  | branch op left right =>
    simp only [Block.rename, blockAction, bind_assoc, pure_bind]
    congr 1
    funext out
    cases out <;> simp only [Sum.elim_inl, Sum.elim_inr, commute]

private theorem split_local (external : List τ) :
    (locals : List τ) → (i : Nat) → {Z : τ} →
    (outside : At (locals ++ external) i Z) → (inside : At locals i Z) → (x : TyDen Z) →
    LabelValue.appendSplit locals external (LabelValue.inject i outside x) =
      .inr (LabelValue.inject i inside x)
  | [], _, _, _, inside, _ => by simp [At] at inside
  | _ :: _, 0, _, _, _, _ => rfl
  | _ :: rest, i + 1, _, outside, inside, x => by
    rw [LabelValue.inject_succ i outside (show At (rest ++ external) i _ from outside),
      LabelValue.inject_succ i inside (show At rest i _ from inside),
      LabelValue.appendSplit, split_local]

private theorem split_external (external : List τ) :
    (locals : List τ) → (i : Nat) → {Z : τ} →
    (outside : At (locals ++ external) (i + locals.length) Z) →
    (inside : At external i Z) → (x : TyDen Z) →
    LabelValue.appendSplit locals external (LabelValue.inject (i + locals.length) outside x) =
      .inl (LabelValue.inject i inside x)
  | [], _, _, _, _, _ => rfl
  | _ :: rest, i, _, outside, inside, x => by
    simp only [List.length_cons, Nat.add_succ]
    rw [LabelValue.inject_succ (i + rest.length) outside (show At (rest ++ external) (i + rest.length) _ from outside),
      LabelValue.appendSplit, split_external]

private noncomputable def route {n : Nat} (R : Fin n → τ) (L : List τ) {I : Type u}
    (encode : FiniteLabelDen R → I) {Z : τ} (target : Site (List.ofFn R ++ L) Z) (x : TyDen Z) :
    LabelDen L ⊕ I :=
  Sum.map id (encode ∘ labelDenToFinite R) (LabelValue.appendSplit (List.ofFn R) L (siteValue target x))

private theorem route_local {n : Nat} (R : Fin n → τ) (L : List τ) {I : Type u}
    (encode : FiniteLabelDen R → I) (i : Fin n) (x : TyDen (R i)) :
    route R L encode (localSite R L i) x = .inr (encode ⟨i,x⟩) := by
  unfold route siteValue
  simp only [localSite]
  rw [split_local L (List.ofFn R) i.val _ (by simp [At]) x]
  rw [Sum.map_inr, Function.comp_apply, labelDenToFinite_recursiveInject]
  rfl

private theorem route_external {n : Nat} (R : Fin n → τ) (L : List τ) {I : Type u}
    (encode : FiniteLabelDen R → I) (i : Fin L.length) (x : TyDen (L.get i)) :
    route R L encode (externalSite R L i) x = .inl (LabelValue.inject i.val
      (List.getElem?_eq_getElem i.isLt) x) := by
  unfold route siteValue
  simp only [externalSite]
  rw [split_external L (List.ofFn R) i.val _ (List.getElem?_eq_getElem i.isLt) x]
  rfl

private theorem cfg_denotes {n : Nat} (R : Fin (n+1) → τ) (L : List τ) {I : Type u}
    (blocks : ∀ i, Block Φ (List.ofFn R ++ L) (R i))
    (start : Site (List.ofFn R ++ L) X) (encode : FiniteLabelDen R → I)
    (step : I → m (LabelDen L ⊕ I)) (initial : TyDen X → I)
    (enter : ∀ x, route R L encode start x = .inr (initial x))
    (dispatch : ∀ i x, blockAction (ε := ε) (m := m) (route R L encode) (blocks i) x =
      step (encode ⟨i,x⟩)) :
    RegionDenotes (m := m) ε
      (.cfg R (.br start.typing (.var (Φ := Φ) (Γ := [X]) (i := 0) rfl))
        (fun i => (blocks i).typing [X]))
      (fun env => iter step (initial env.2)) := by
  let entry : Env [X] → m (LabelDen (List.ofFn R ++ L)) := fun e => pure (siteValue start e.2)
  let actions i (e : Env (R i :: [X])) := blockAction (ε := ε) (m := m) siteValue (blocks i) e.2
  let collect (p : Env [X] × FiniteLabelDen R) := actions p.2.1 (p.1,p.2.2)
  have agrees : CollectiveDenotes [X] R L actions collect := ⟨fun _ _ _ => rfl⟩
  have den := RegionDenotes.cfg _ _ (branch_denotes (m := m) (ε := ε) (Γ := []) start)
    (fun i => block_denotes (m := m) (ε := ε) (Γ := [X]) (blocks i)) agrees
  suffices eq : cfgDenotation (R := R) entry collect = fun env => iter step (initial env.2) by
    rwa [← eq]
  funext env
  let raw : LabelDen (List.ofFn R) → m (LabelDen L ⊕ LabelDen (List.ofFn R)) :=
    fun l => collect (env, labelDenToFinite R l) >>= fun r => pure (LabelValue.appendSplit _ _ r)
  let loc := encode ∘ labelDenToFinite R
  have square : (raw >=> liftPure (Sum.map id loc)) = (liftPure loc >=> step) := by
    funext l
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, raw, bind_assoc]
    change _ = step (encode (labelDenToFinite R l))
    obtain ⟨i, x⟩ := labelDenToFinite R l
    change (blockAction (ε := ε) (m := m) siteValue (blocks i) x >>= fun r =>
      pure (Sum.map id (encode ∘ labelDenToFinite R) (LabelValue.appendSplit (List.ofFn R) L r))) =
        step (encode ⟨i,x⟩)
    rw [← dispatch i x]
    have identity : (blocks i).rename (fun s => s) = blocks i := by
      cases blocks i <;> rfl
    simpa only [identity] using (block_map (ε := ε) (m := m) (blocks i) x (fun s => s)
      siteValue (route R L encode)
      (fun l => Sum.map id loc (LabelValue.appendSplit (List.ofFn R) L l)) (fun _ _ => rfl)).symm
  let split := LabelValue.appendSplit (List.ofFn R) L (siteValue start env.2)
  have startCase : Sum.map id loc split = .inr (initial env.2) := enter env.2
  simp only [cfgDenotation, entry, pure_bind, binaryCoproductIso_hom_labelAppendSplit]
  rw [show LabelValue.appendSplit (List.ofFn R) L (siteValue start env.2) = split from rfl]
  cases eq : split with
  | inl l => simp [eq] at startCase
  | inr x =>
    have hx : loc x = initial env.2 := by simpa [eq] using startCase
    exact (congrFun (LawfulElgotMonad.uniformity raw step loc square) x).trans
      (by simp [Bind.kleisliRight, liftPure, hx])

private noncomputable def step (s : Loop Φ A B K E D)
    (p : FiniteLabelDen (Theta.localTypes s)) : m (LabelDen [E,D] ⊕ FiniteLabelDen (Theta.localTypes s)) :=
  blockAction (ε := ε) (route (Theta.localTypes s) [E,D] id) (Theta.blockAt s p.1) p.2

private theorem single_denotes (s : Loop Φ A B K E D) :
    RegionDenotes (m := m) ε (Theta.regionTyping s) (fun env => iter (step (ε := ε) s) ⟨0, env.2⟩) :=
  cfg_denotes _ _ (Theta.blockAt s) (localSite (Theta.localTypes s) [E,D] 0)
    id (step (ε := ε) s) (fun x => ⟨0,x⟩) (route_local _ _ id 0) (fun _ _ => rfl)

variable (s : Loops Φ A B K M C J E D)

private abbrev Local1 := FiniteLabelDen (Theta.localTypes s.first)
private abbrev Local2 := FiniteLabelDen (Theta.localTypes s.second)

private def phaseAt : (i : Fin (firstCount s + secondCount s)) →
    TyDen (localTypes s i) → Local1 s ⊕ Local2 s :=
  Fin.addCases (motive := fun i => TyDen (localTypes s i) → Local1 s ⊕ Local2 s)
    (fun i x => .inl ⟨i, first_type s i ▸ x⟩)
    (fun i x => .inr ⟨i, second_type s i ▸ x⟩)

private def encode (p : FiniteLabelDen (localTypes s)) : Local1 s ⊕ Local2 s := phaseAt s p.1 p.2

private theorem route_cast {n : Nat} (R : Fin n → τ) (L : List τ) {I : Type u}
    (encode : FiniteLabelDen R → I) (h : X = Y) (target : Site (List.ofFn R ++ L) X) (x : TyDen Y) :
    route R L encode (h ▸ target) x = route R L encode target (h.symm ▸ x) := by
  cases h
  rfl

private theorem payload_cast_cancel (h : X = Y) (y : TyDen Y) :
    h ▸ (h.symm ▸ y : TyDen X) = y := by
  cases h
  rfl

private theorem first_route (i : Fin (firstCount s)) (x : TyDen (Theta.localTypes s.first i)) :
    route (localTypes s) [E,D] (encode s) (firstLocal s i) x = .inr (.inl ⟨i,x⟩) := by
  rw [firstLocal, route_cast, route_local]
  simp only [encode, phaseAt, Fin.addCases_left, payload_cast_cancel]

private theorem second_route (i : Fin (secondCount s)) (x : TyDen (Theta.localTypes s.second i)) :
    route (localTypes s) [E,D] (encode s) (secondLocal s i) x = .inr (.inr ⟨i,x⟩) := by
  rw [secondLocal, route_cast, route_local]
  simp only [encode, phaseAt, Fin.addCases_right, payload_cast_cancel]

private def leftTarget (r : LabelDen [M,M] ⊕ Local1 s) : LabelDen [E,D] ⊕ (Local1 s ⊕ Local2 s) :=
  .inr (Sum.elim (Sum.inr ∘ fun label => ⟨0, merge label⟩) Sum.inl r)

private def rightTarget : LabelDen [E,D] ⊕ Local2 s → LabelDen [E,D] ⊕ (Local1 s ⊕ Local2 s) :=
  Sum.map id Sum.inr

private theorem left_route (target : Site (Theta.Labels s.first) X) (x : TyDen X) :
    route (localTypes s) [E,D] (encode s) (leftSite s target) x =
      leftTarget s (route (Theta.localTypes s.first) [M,M] id target x) := by
  unfold leftSite redirect
  generalize eq : splitSite (Theta.localTypes s.first) [M,M] target = split
  obtain ⟨whereTo, eqSite⟩ := split
  subst target
  cases whereTo with
  | «local» i =>
    change route (localTypes s) [E,D] (encode s) (firstLocal s i) x =
      leftTarget s (route (Theta.localTypes s.first) [M,M] id (localSite _ _ i) x)
    rw [route_local, first_route]
    rfl
  | external i =>
    change _ = leftTarget s (route (Theta.localTypes s.first) [M,M] id (externalSite _ _ i) x)
    rw [route_external]
    revert x
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i <;> intro x
    · exact second_route s 0 x
    · exact second_route s 0 x

private theorem right_route (target : Site (Theta.Labels s.second) X) (x : TyDen X) :
    route (localTypes s) [E,D] (encode s) (rightSite s target) x =
      rightTarget s (route (Theta.localTypes s.second) [E,D] id target x) := by
  unfold rightSite redirect
  generalize eq : splitSite (Theta.localTypes s.second) [E,D] target = split
  obtain ⟨whereTo, eqSite⟩ := split
  subst target
  cases whereTo with
  | «local» i =>
    change route (localTypes s) [E,D] (encode s) (secondLocal s i) x =
      rightTarget s (route (Theta.localTypes s.second) [E,D] id (localSite _ _ i) x)
    rw [route_local, second_route]
    rfl
  | external i =>
    change route (localTypes s) [E,D] (encode s) (externalSite _ _ i) x =
      rightTarget s (route (Theta.localTypes s.second) [E,D] id (externalSite _ _ i) x)
    rw [route_external, route_external]
    rfl

private noncomputable def flatStep : Local1 s ⊕ Local2 s → m (LabelDen [E,D] ⊕ (Local1 s ⊕ Local2 s))
  | .inl p => step (ε := ε) s.first p >>= fun r => pure (leftTarget s r)
  | .inr p => step (ε := ε) s.second p >>= fun r => pure (rightTarget s r)

omit [LawfulMonad m] [Iterate m] [LawfulElgotMonad m] in
private theorem action_cast {R : List τ} {I : Type u}
    (dest : ∀ {Z}, Site R Z → TyDen Z → I) (h : X = Y) (b : Block Φ R X) (y : TyDen Y) :
    blockAction (ε := ε) (m := m) dest (h ▸ b) y = blockAction (ε := ε) dest b (h.symm ▸ y) := by
  cases h
  rfl

omit [Iterate m] [LawfulElgotMonad m] in
private theorem dispatch (i : Fin (firstCount s + secondCount s)) (x : TyDen (localTypes s i)) :
    blockAction (ε := ε) (m := m) (route (localTypes s) [E,D] (encode s)) (blockAt s i) x =
      flatStep (ε := ε) s (encode s ⟨i,x⟩) := by
  revert x
  refine Fin.addCases ?_ ?_ i
  · intro i x
    simp only [blockAt, encode, phaseAt, Fin.addCases_left, action_cast, flatStep, step]
    exact block_map (Theta.blockAt s.first i) _ (leftSite s) _ _ _ (left_route s)
  · intro i x
    simp only [blockAt, encode, phaseAt, Fin.addCases_right, action_cast, flatStep, step]
    exact block_map (Theta.blockAt s.second i) _ (rightSite s) _ _ _ (right_route s)

private theorem flat_denotes :
    RegionDenotes (m := m) ε (regionTyping s) (fun env =>
      iter (flatStep (ε := ε) s) (.inl ⟨0,env.2⟩)) := by
  apply cfg_denotes _ _ (blockAt s) (firstEntry s) (encode s) (flatStep (ε := ε) s)
    (fun x => .inl ⟨0,x⟩)
  · exact first_route s 0
  · exact dispatch s

open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

theorem region_sequential
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTyping s) env =
      Region.denote (ε := ε) (m := m) (Theta.regionTyping s.first) env >>= fun mid =>
        Region.denote (ε := ε) (m := m) (Theta.regionTyping s.second) (PUnit.unit, merge mid) := by
  rw [TwoBlock.regionDenote_eq_of coherent (flat_denotes s),
    TwoBlock.regionDenote_eq_of coherent (single_denotes s.first),
    TwoBlock.regionDenote_eq_of coherent (single_denotes s.second)]
  exact iter_sequential (step (ε := ε) s.first) (step (ε := ε) s.second) (fun label => ⟨0, merge label⟩)
    (flatStep (ε := ε) s) (fun _ => rfl) (fun _ => rfl) _

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Proofs
