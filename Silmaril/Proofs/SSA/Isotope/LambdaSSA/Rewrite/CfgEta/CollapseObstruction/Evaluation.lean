module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CollapseObstruction.Frame
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.CollapseObstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! # Typing and value substitution for coloured observations -/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open scoped Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)

abbrev Env := Nat → Val

def evalTerm : Tm Empty → Env → Option Val
  | .var i, env => some (env i)
  | .op p _, _ => p.elim
  | .let₁ x t, env => do
      let v ← evalTerm x env
      evalTerm t (extend env v)
  | .unit, _ => some .unit
  | .pair x y, env => do
      let v ← evalTerm x env
      let w ← evalTerm y env
      pure (.pair v w)
  | .let₂ x t, env => do
      let .pair v w ← evalTerm x env | none
      evalTerm t (extend (extend env v) w)
  | .inl x, env => (evalTerm x env).map Value.inl
  | .inr x, env => (evalTerm x env).map Value.inr
  | .case x l r, env => match evalTerm x env with
      | some (.inl v) => evalTerm l (extend env v)
      | some (.inr v) => evalTerm r (extend env v)
      | _ => none
  | .abort _, _ => none

noncomputable def evalRegion : Region Empty → Env → Result
  | .br i t, env => match evalTerm t env with
      | some v => .jump i v
      | none => .fault
  | .let₁ x r, env => match evalTerm x env with
      | some v => evalRegion r (extend env v)
      | _ => .fault
  | .let₂ x r, env => match evalTerm x env with
      | some (.pair v w) => evalRegion r (extend (extend env v) w)
      | _ => .fault
  | .case x l r, env => match evalTerm x env with
      | some (.inl v) => evalRegion l (extend env v)
      | some (.inr v) => evalRegion r (extend env v)
      | _ => .fault
  | .cfg e n bs, env => cfgRun n (fun i v => evalRegion (bs i) (extend env v)) (evalRegion e env)

theorem evalTerm_rename (t : Tm Empty) {env env' : Env} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) : evalTerm (t.rename ρ) env' = evalTerm t env := by
  induction t generalizing env env' ρ with
  | var i => simp only [Tm.rename, evalTerm, h]
  | op p _ _ => exact p.elim
  | let₁ x t ix it =>
    simp only [Tm.rename, evalTerm, ix h]
    cases evalTerm x env with
    | none => rfl
    | some v => exact it (extend_rename h v)
  | pair _ _ ix iy => simp only [Tm.rename, evalTerm, ix h, iy h]
  | unit => rfl
  | let₂ x t ix it =>
    simp only [Tm.rename, evalTerm, ix h]
    cases evalTerm x env with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      exact it (extend_rename (extend_rename h _) _)
  | inl _ ix => simp only [Tm.rename, evalTerm, ix h]
  | inr _ ix => simp only [Tm.rename, evalTerm, ix h]
  | case x l r ix il ir =>
    simp only [Tm.rename, evalTerm, ix h]
    cases evalTerm x env with
    | none => rfl
    | some v =>
      cases v <;> first | rfl | exact il (extend_rename h _) | exact ir (extend_rename h _)
  | abort _ _ => rfl

def Realizes (env env' : Env) (θ : Nat → Tm Empty) : Prop :=
  ∀ i, evalTerm (θ i) env = some (env' i)

theorem Realizes.lift {env env' : Env} {θ : Nat → Tm Empty} (h : Realizes env env' θ) (v : Val) :
    Realizes (extend env v) (extend env' v) (Tm.liftSubst θ) := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
    change evalTerm ((θ i).rename Nat.succ) (extend env v) = some (env' i)
    rw [evalTerm_rename (θ i) (env := env) (env' := extend env v) (ρ := Nat.succ) (fun _ => rfl)]
    exact h i

theorem evalTerm_subst (t : Tm Empty) {env env' : Env} {θ : Nat → Tm Empty}
    (h : Realizes env env' θ) : evalTerm (t.subst θ) env = evalTerm t env' := by
  induction t generalizing env env' θ with
  | var i => exact h i
  | op p _ _ => exact p.elim
  | let₁ x t ix it =>
    simp only [Tm.subst, evalTerm, ix h]
    cases evalTerm x env' with
    | none => rfl
    | some v => exact it (h.lift v)
  | pair _ _ ix iy => simp only [Tm.subst, evalTerm, ix h, iy h]
  | unit => rfl
  | let₂ x t ix it =>
    simp only [Tm.subst, evalTerm, ix h]
    cases evalTerm x env' with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      exact it ((h.lift _).lift _)
  | inl _ ix => simp only [Tm.subst, evalTerm, ix h]
  | inr _ ix => simp only [Tm.subst, evalTerm, ix h]
  | case x l r ix il ir =>
    simp only [Tm.subst, evalTerm, ix h]
    cases evalTerm x env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift _) | exact ir (h.lift _)
  | abort _ _ => rfl

theorem evalRegion_subst (r : Region Empty) {env env' : Env} {θ : Nat → Tm Empty}
    (h : Realizes env env' θ) : evalRegion (r.substVars θ) env = evalRegion r env' := by
  induction r generalizing env env' θ with
  | br i t => simp only [substVars, evalRegion, evalTerm_subst t h]
  | let₁ x r ih =>
    simp only [substVars, evalRegion, evalTerm_subst x h]
    cases evalTerm x env' with
    | none => rfl
    | some v => exact ih (h.lift v)
  | let₂ x r ih =>
    simp only [substVars, evalRegion, evalTerm_subst x h]
    cases evalTerm x env' with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      exact ih ((h.lift _).lift _)
  | case x l r il ir =>
    simp only [substVars, evalRegion, evalTerm_subst x h]
    cases evalTerm x env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift _) | exact ir (h.lift _)
  | cfg e n bs ie ib =>
    simp only [substVars, evalRegion, ie h]
    congr 1
    funext i v
    exact ib i (h.lift v)

theorem evalRegion_renameVars (r : Region Empty) {env env' : Env} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) : evalRegion (r.renameVars ρ) env' = evalRegion r env := by
  rw [renameVars_eq_substVars]
  exact evalRegion_subst r (fun i => congrArg some (h i))

theorem Realizes.single {env : Env} {t : Tm Empty} {v : Val} (h : evalTerm t env = some v) :
    Realizes env (extend env v) (Tm.singleSubst t) := by
  intro i
  cases i with
  | zero => exact h
  | succ i => rfl

inductive ValTy : Val → Ty Empty → Prop where
  | unit : ValTy .unit .unit
  | pair {a b : Val} {A B : Ty Empty} :
      ValTy a A → ValTy b B → ValTy (.pair a b) (.product A B)
  | inl {a : Val} {A B : Ty Empty} : ValTy a A → ValTy (.inl a) (.coprod A B)
  | inr {b : Val} {A B : Ty Empty} : ValTy b B → ValTy (.inr b) (.coprod A B)

def EnvTy (Γ : VCtx (Ty Empty)) (env : Env) : Prop :=
  ∀ ⦃i A⦄, At Γ i A → ValTy (env i) A

theorem EnvTy.extend {Γ : VCtx (Ty Empty)} {A : Ty Empty} {env : Env} {v : Val}
    (h : EnvTy Γ env) (hv : ValTy v A) : EnvTy (A :: Γ) (extend env v) := by
  intro i D hi
  cases i with
  | zero => cases Option.some.inj hi; exact hv
  | succ i => exact h hi

theorem evalTerm_typed {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.HasType Γ t A) {env : Env} (h : EnvTy Γ env) :
    ∃ v, evalTerm t env = some v ∧ ValTy v A := by
  induction ht generalizing env with
  | var hi => exact ⟨_, rfl, h hi⟩
  | @op _ _ f _ _ => exact f.elim
  | let₁ _ _ ix it =>
    obtain ⟨v, eq, hv⟩ := ix h
    obtain ⟨w, eq', hw⟩ := it (h.extend hv)
    exact ⟨w, by simp [evalTerm, eq, eq'], hw⟩
  | pair _ _ ix iy =>
    obtain ⟨v, eq, hv⟩ := ix h
    obtain ⟨w, eq', hw⟩ := iy h
    exact ⟨.pair v w, by simp [evalTerm, eq, eq'], .pair hv hw⟩
  | unit => exact ⟨.unit, rfl, .unit⟩
  | let₂ _ _ ix it =>
    obtain ⟨v, eq, hv⟩ := ix h
    cases hv with
    | pair ha hb =>
      obtain ⟨w, eq', hw⟩ := it ((h.extend ha).extend hb)
      exact ⟨w, by simp [evalTerm, eq, eq'], hw⟩
  | inl _ it =>
    obtain ⟨v, eq, hv⟩ := it h
    exact ⟨.inl v, by simp [evalTerm, eq], .inl hv⟩
  | inr _ it =>
    obtain ⟨v, eq, hv⟩ := it h
    exact ⟨.inr v, by simp [evalTerm, eq], .inr hv⟩
  | case _ _ _ ix il ir =>
    obtain ⟨v, eq, hv⟩ := ix h
    cases hv with
    | inl hv =>
      obtain ⟨w, eq', hw⟩ := il (h.extend hv)
      exact ⟨w, by simp [evalTerm, eq, eq'], hw⟩
    | inr hv =>
      obtain ⟨w, eq', hw⟩ := ir (h.extend hv)
      exact ⟨w, by simp [evalTerm, eq, eq'], hw⟩
  | abort _ ix =>
    obtain ⟨_, _, hv⟩ := ix h
    cases hv

def ResultTy (L : LCtx (Ty Empty)) : Result → Prop
  | .jump i v => ∃ A, At L i A ∧ ValTy v A
  | .diverges _ => True
  | .fault => False

def FrameTy {n : Nat} (R : Fin n → Ty Empty) (L : LCtx (Ty Empty)) : Frame n → Prop
  | .inl r => ResultTy L r
  | .inr (i, v) => ValTy v (R i)

theorem enter_typed {n : Nat} (R : Fin n → Ty Empty) {L : LCtx (Ty Empty)} {r : Result}
    (h : ResultTy (List.ofFn R ++ L) r) : FrameTy R L (enter n r) := by
  cases r with
  | jump i v =>
    obtain ⟨A, hi, hv⟩ := h
    by_cases hlt : i < n
    · rw [enter, dite_eq_left hlt]
      change ValTy v (R ⟨i, hlt⟩)
      have he : i < (List.ofFn R).length := by simpa only [List.length_ofFn] using hlt
      have hR : At (List.ofFn R) i (R ⟨i, hlt⟩) := by simp [At, List.getElem?_eq_getElem he]
      rw [At, List.getElem?_append_left he] at hi
      cases Option.some.inj (hi.symm.trans hR)
      exact hv
    · rw [enter, dite_eq_right hlt]
      have he : (List.ofFn R).length ≤ i := by
        simpa only [List.length_ofFn] using Nat.le_of_not_gt hlt
      rw [At, List.getElem?_append_right he, List.length_ofFn] at hi
      exact ⟨A, hi, hv⟩
  | diverges _ => trivial
  | fault => exact h.elim

theorem step_typed {n : Nat} (R : Fin n → Ty Empty) (L : LCtx (Ty Empty))
    {bs : Fin n → Val → Result} (hbs : ∀ i v, ValTy v (R i) → ResultTy (List.ofFn R ++ L) (bs i v))
    (s : Frame n) (hs : FrameTy R L s) : FrameTy R L (step bs s) := by
  cases s with
  | inl r => exact hs
  | inr s =>
    obtain ⟨i, v⟩ := s
    exact enter_typed R (hbs i v hs)

theorem cfgRun_typed {n : Nat} (R : Fin n → Ty Empty) (L : LCtx (Ty Empty))
    {bs : Fin n → Val → Result} {r : Result}
    (he : ResultTy (List.ofFn R ++ L) r)
    (hb : ∀ i v, ValTy v (R i) → ResultTy (List.ofFn R ++ L) (bs i v)) :
    ResultTy L (cfgRun n bs r) := by
  classical
  have good (i : Nat) : FrameTy R L (path bs (enter n r) i) := by
    induction i with
    | zero => exact enter_typed R he
    | succ i ih => exact step_typed R L hb _ ih
  by_cases hex : ∃ r', terminates bs (enter n r) r'
  · obtain ⟨r', i, hi⟩ := hex
    have h := good i
    rw [hi] at h
    change ResultTy L (finish bs (enter n r))
    rw [finish_of_terminal bs _ hi]
    exact h
  · change ResultTy L (finish bs (enter n r))
    rw [finish, dite_eq_right hex]
    split <;> trivial

theorem evalRegion_typed {Γ : VCtx (Ty Empty)} {r : Region Empty} {L : LCtx (Ty Empty)}
    (hr : HasType Γ r L) {env : Env} (h : EnvTy Γ env) : ResultTy L (evalRegion r env) := by
  induction hr generalizing env with
  | br hi ht =>
    obtain ⟨v, eq, hv⟩ := evalTerm_typed ht h
    rw [evalRegion, eq]
    exact ⟨_, hi, hv⟩
  | let₁ ht _ ih =>
    obtain ⟨v, eq, hv⟩ := evalTerm_typed ht h
    rw [evalRegion, eq]
    exact ih (h.extend hv)
  | let₂ ht _ ih =>
    obtain ⟨v, eq, hv⟩ := evalTerm_typed ht h
    cases hv with
    | pair ha hb =>
      rw [evalRegion, eq]
      exact ih ((h.extend ha).extend hb)
  | case ht _ _ il ir =>
    obtain ⟨v, eq, hv⟩ := evalTerm_typed ht h
    cases hv with
    | inl hv =>
      rw [evalRegion, eq]
      exact il (h.extend hv)
    | inr hv =>
      rw [evalRegion, eq]
      exact ir (h.extend hv)
  | cfg R _ _ ie ib =>
    rw [evalRegion]
    exact cfgRun_typed R _ (ie h) (fun i _ hv => ib i (h.extend hv))

theorem mapTerminal_id {n : Nat} (s : Frame n) : mapTerminal id s = s := by cases s <;> rfl

theorem cfgRun_congr {n : Nat} (R : Fin n → Ty Empty) (L : LCtx (Ty Empty))
    {bs bs' : Fin n → Val → Result} {r : Result}
    (he : ResultTy (List.ofFn R ++ L) r)
    (typed : ∀ i v, ValTy v (R i) → ResultTy (List.ofFn R ++ L) (bs i v))
    (hb : ∀ i v, ValTy v (R i) → bs i v = bs' i v) :
    cfgRun n bs r = cfgRun n bs' r := by
  have comm (s : Frame n) (hs : FrameTy R L s) : step bs' s = step bs s := by
    cases s with
    | inl _ => rfl
    | inr s =>
      obtain ⟨i, v⟩ := s
      change enter n (bs' i v) = enter n (bs i v)
      rw [hb i v hs]
  have hh := finish_mapTerminalOn bs bs' id (fun _ => rfl) (FrameTy R L)
    (step_typed R L typed) (fun s hs => by simp only [mapTerminal_id]; exact comm s hs)
    (enter n r) (enter_typed R he)
  simpa only [mapTerminal_id, id_eq, cfgRun] using hh.symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence
