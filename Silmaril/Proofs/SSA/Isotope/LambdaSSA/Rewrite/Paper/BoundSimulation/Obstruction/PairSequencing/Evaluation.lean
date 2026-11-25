module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Evaluation

/-! # Evaluation that distinguishes unary lets in pair operands

This observer sequences a term let at the root. A pair faults if either
operand starts with a unary let. This head test is stable under the
constructor substitutions used by the equational rules.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Paper.BoundSimulation.Obstruction
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (Env EnvTy Val ValTy Result ResultTy cfgRun
  cfgRun_typed)

def startsLet : Tm Empty → Bool
  | .let₁ _ _ => true
  | _ => false

theorem startsLet_rename (t : Tm Empty) (ρ : Nat → Nat) :
    startsLet (t.rename ρ) = startsLet t := by
  cases t <;> rfl

theorem startsLet_subst (t : Tm Empty) (θ : Nat → Tm Empty)
    (hθ : ∀ i, startsLet (θ i) = false) :
    startsLet (t.subst θ) = startsLet t := by
  cases t with
  | var i => exact hθ i
  | _ => rfl

theorem startsLet_substOn {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.HasType Γ t A) {θ : Nat → Tm Empty}
    (hθ : ∀ i A, At Γ i A → startsLet (θ i) = false) :
    startsLet (t.subst θ) = startsLet t := by
  cases ht with
  | var hi => exact hθ _ _ hi
  | _ => rfl

theorem value_startsLet {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue Γ t A) : startsLet t = false := by cases ht <;> rfl

/-- The marked observer faults at an immediate unary-let pair operand.
The unmarked observer evaluates both pair operands in order. -/
def evalTermWith (markPairLet : Bool) : Tm Empty → Env → Option Val
  | .var i, env => some (env i)
  | .op p _, _ => p.elim
  | .let₁ x t, env => do
      let v ← evalTermWith markPairLet x env
      evalTermWith markPairLet t (extend env v)
  | .unit, _ => some .unit
  | .pair x y, env =>
      if markPairLet && (startsLet x || startsLet y) then none
      else do
        let v ← evalTermWith markPairLet x env
        let w ← evalTermWith markPairLet y env
        pure (.pair v w)
  | .let₂ x t, env => do
      let .pair v w ← evalTermWith markPairLet x env | none
      evalTermWith markPairLet t (extend (extend env v) w)
  | .inl x, env => (evalTermWith markPairLet x env).map Value.inl
  | .inr x, env => (evalTermWith markPairLet x env).map Value.inr
  | .case x l r, env => match evalTermWith markPairLet x env with
      | some (.inl v) => evalTermWith markPairLet l (extend env v)
      | some (.inr v) => evalTermWith markPairLet r (extend env v)
      | _ => none
  | .abort _, _ => none

noncomputable def evalRegionWith (markPairLet : Bool) : Region Empty → Env → Result
  | .br i t, env => match evalTermWith markPairLet t env with
      | some v => .jump i v
      | none => .fault
  | .let₁ x r, env => match evalTermWith markPairLet x env with
      | some v => evalRegionWith markPairLet r (extend env v)
      | _ => .fault
  | .let₂ x r, env => match evalTermWith markPairLet x env with
      | some (.pair v w) => evalRegionWith markPairLet r (extend (extend env v) w)
      | _ => .fault
  | .case x l r, env => match evalTermWith markPairLet x env with
      | some (.inl v) => evalRegionWith markPairLet l (extend env v)
      | some (.inr v) => evalRegionWith markPairLet r (extend env v)
      | _ => .fault
  | .cfg e n bs, env => cfgRun n (fun i v => evalRegionWith markPairLet (bs i) (extend env v)) (evalRegionWith markPairLet e env)

variable {markPairLet : Bool}

local notation "evalTerm" => evalTermWith markPairLet
local notation "evalRegion" => evalRegionWith markPairLet

theorem evalTerm_rename (t : Tm Empty) {env env' : Env} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) : evalTerm (t.rename ρ) env' = evalTerm t env := by
  induction t generalizing env env' ρ with
  | var i => simp only [Tm.rename, evalTermWith, h]
  | op p _ _ => exact p.elim
  | let₁ x t ix it =>
    simp only [Tm.rename, evalTermWith, ix h]
    cases evalTerm x env with
    | none => rfl
    | some v => exact it (extend_rename h v)
  | pair _ _ ix iy => simp only [Tm.rename, evalTermWith, startsLet_rename, ix h, iy h]
  | unit => rfl
  | let₂ x t ix it =>
    simp only [Tm.rename, evalTermWith, ix h]
    cases evalTerm x env with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      exact it (extend_rename (extend_rename h _) _)
  | inl _ ix => simp only [Tm.rename, evalTermWith, ix h]
  | inr _ ix => simp only [Tm.rename, evalTermWith, ix h]
  | case x l r ix il ir =>
    simp only [Tm.rename, evalTermWith, ix h]
    cases evalTerm x env with
    | none => rfl
    | some v =>
      cases v <;> first | rfl | exact il (extend_rename h _) | exact ir (extend_rename h _)
  | abort _ _ => rfl

def RealizesWith (markPairLet : Bool) (env env' : Env) (θ : Nat → Tm Empty) : Prop :=
  ∀ i, evalTermWith markPairLet (θ i) env = some (env' i) ∧ startsLet (θ i) = false

local notation "Realizes" => RealizesWith markPairLet

theorem RealizesWith.lift {env env' : Env} {θ : Nat → Tm Empty} (h : Realizes env env' θ) (v : Val) :
    Realizes (extend env v) (extend env' v) (Tm.liftSubst θ) := by
  intro i
  cases i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i =>
    change evalTerm ((θ i).rename Nat.succ) (extend env v) = some (env' i) ∧
      startsLet ((θ i).rename Nat.succ) = false
    rw [evalTerm_rename (θ i) (env := env) (env' := extend env v) (ρ := Nat.succ) (fun _ => rfl)]
    rw [startsLet_rename]
    exact h i

theorem evalTerm_subst (t : Tm Empty) {env env' : Env} {θ : Nat → Tm Empty}
    (h : Realizes env env' θ) : evalTerm (t.subst θ) env = evalTerm t env' := by
  induction t generalizing env env' θ with
  | var i => exact (h i).1
  | op p _ _ => exact p.elim
  | let₁ x t ix it =>
    simp only [Tm.subst, evalTermWith, ix h]
    cases evalTerm x env' with
    | none => rfl
    | some v => exact it (h.lift v)
  | pair a b ix iy =>
    simp only [Tm.subst, evalTermWith, startsLet_subst a θ (fun i => (h i).2),
      startsLet_subst b θ (fun i => (h i).2), ix h, iy h]
  | unit => rfl
  | let₂ x t ix it =>
    simp only [Tm.subst, evalTermWith, ix h]
    cases evalTerm x env' with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      exact it ((h.lift _).lift _)
  | inl _ ix => simp only [Tm.subst, evalTermWith, ix h]
  | inr _ ix => simp only [Tm.subst, evalTermWith, ix h]
  | case x l r ix il ir =>
    simp only [Tm.subst, evalTermWith, ix h]
    cases evalTerm x env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift _) | exact ir (h.lift _)
  | abort _ _ => rfl

theorem evalRegion_subst (r : Region Empty) {env env' : Env} {θ : Nat → Tm Empty}
    (h : Realizes env env' θ) : evalRegion (r.substVars θ) env = evalRegion r env' := by
  induction r generalizing env env' θ with
  | br i t => simp only [substVars, evalRegionWith, evalTerm_subst t h]
  | let₁ x r ih =>
    simp only [substVars, evalRegionWith, evalTerm_subst x h]
    cases evalTerm x env' with
    | none => rfl
    | some v => exact ih (h.lift v)
  | let₂ x r ih =>
    simp only [substVars, evalRegionWith, evalTerm_subst x h]
    cases evalTerm x env' with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      exact ih ((h.lift _).lift _)
  | case x l r il ir =>
    simp only [substVars, evalRegionWith, evalTerm_subst x h]
    cases evalTerm x env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift _) | exact ir (h.lift _)
  | cfg e n bs ie ib =>
    simp only [substVars, evalRegionWith, ie h]
    congr 1
    funext i v
    exact ib i (h.lift v)

theorem evalRegion_renameVars (r : Region Empty) {env env' : Env} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) : evalRegion (r.renameVars ρ) env' = evalRegion r env := by
  rw [renameVars_eq_substVars]
  exact evalRegion_subst r (fun i => ⟨congrArg some (h i), rfl⟩)

theorem RealizesWith.single {env : Env} {t : Tm Empty} {v : Val} (h : evalTerm t env = some v)
    (ht : startsLet t = false) : Realizes env (extend env v) (Tm.singleSubst t) := by
  intro i
  cases i with
  | zero => exact ⟨h, ht⟩
  | succ i => exact ⟨rfl, rfl⟩

theorem evalTerm_typed {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.HasType Γ t A) {env : Env} (h : EnvTy Γ env) {v : Val}
    (he : evalTerm t env = some v) : ValTy v A := by
  induction ht generalizing env v with
  | var hi => cases Option.some.inj he; exact h hi
  | @op _ _ f _ _ => exact f.elim
  | @let₁ _ a _ _ _ _ _ ia ib =>
    cases hx : evalTerm a env with
    | none => simp [evalTermWith, hx] at he
    | some x => exact ib (h.extend (ia h hx)) (by simpa [evalTermWith, hx] using he)
  | @pair _ a b _ _ _ _ ix iy =>
    by_cases guard : (markPairLet && (startsLet a || startsLet b)) = true
    · simp [evalTermWith, guard] at he
    · cases hx : evalTerm a env with
      | none => simp [evalTermWith, guard, hx] at he
      | some x =>
        cases hy : evalTerm b env with
        | none => simp [evalTermWith, guard, hx, hy] at he
        | some y =>
          simp [evalTermWith, guard, hx, hy] at he
          subst v
          exact .pair (ix h hx) (iy h hy)
  | unit => cases Option.some.inj he; exact .unit
  | @let₂ _ a _ _ _ _ _ _ ix it =>
    cases hx : evalTerm a env with
    | none => simp [evalTermWith, hx] at he
    | some x =>
      cases ix h hx with
      | pair ha hb => exact it ((h.extend ha).extend hb) (by simpa [evalTermWith, hx] using he)
  | @inl _ a _ _ _ it =>
    cases hx : evalTerm a env with
    | none => simp [evalTermWith, hx] at he
    | some x =>
      simp [evalTermWith, hx] at he
      subst v
      exact .inl (it h hx)
  | @inr _ a _ _ _ it =>
    cases hx : evalTerm a env with
    | none => simp [evalTermWith, hx] at he
    | some x =>
      simp [evalTermWith, hx] at he
      subst v
      exact .inr (it h hx)
  | @case _ a _ _ _ _ _ _ _ _ ix il ir =>
    cases hx : evalTerm a env with
    | none => simp [evalTermWith, hx] at he
    | some x =>
      cases ix h hx with
      | inl hv => exact il (h.extend hv) (by simpa [evalTermWith, hx] using he)
      | inr hv => exact ir (h.extend hv) (by simpa [evalTermWith, hx] using he)
  | abort => cases he

theorem evalValue {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue Γ t A) {env : Env} (h : EnvTy Γ env) :
    ∃ v, evalTerm t env = some v ∧ ValTy v A := by
  induction ht with
  | var hi => exact ⟨_, rfl, h hi⟩
  | unit => exact ⟨_, rfl, .unit⟩
  | pair ha hb ix iy =>
    obtain ⟨x, hx, hxt⟩ := ix
    obtain ⟨y, hy, hyt⟩ := iy
    exact ⟨_, by simp [evalTermWith, value_startsLet ha, value_startsLet hb, hx, hy], .pair hxt hyt⟩
  | inl _ it =>
    obtain ⟨x, hx, hxt⟩ := it
    exact ⟨_, by simp [evalTermWith, hx], .inl hxt⟩
  | inr _ it =>
    obtain ⟨x, hx, hxt⟩ := it
    exact ⟨_, by simp [evalTermWith, hx], .inr hxt⟩

theorem evalRegion_typed {Γ : VCtx (Ty Empty)} {r : Region Empty} {L : LCtx (Ty Empty)}
    (hr : HasType Γ r L) {env : Env} (h : EnvTy Γ env) : ResultTy L (evalRegion r env) := by
  induction hr generalizing env with
  | br hi ht =>
    rw [evalRegionWith]
    split
    · exact ⟨_, hi, evalTerm_typed ht h (by assumption)⟩
    · trivial
  | let₁ ht _ ih =>
    rw [evalRegionWith]
    split
    · exact ih (h.extend (evalTerm_typed ht h (by assumption)))
    · trivial
  | let₂ ht _ ih =>
    rw [evalRegionWith]
    split
    · have hv := evalTerm_typed ht h (by assumption)
      cases hv with
      | pair ha hb => exact ih ((h.extend ha).extend hb)
    · trivial
  | case ht _ _ il ir =>
    rw [evalRegionWith]
    split
    · have hv := evalTerm_typed ht h (by assumption)
      cases hv with
      | inl ha => exact il (h.extend ha)
    · have hv := evalTerm_typed ht h (by assumption)
      cases hv with
      | inr hb => exact ir (h.extend hb)
    · trivial
  | cfg R _ _ ie ib =>
    rw [evalRegionWith]
    exact cfgRun_typed R _ (ie h) (fun i _ hv => ib i (h.extend hv))

def RealizesOnWith (markPairLet : Bool) (Γ : VCtx (Ty Empty)) (env env' : Env) (θ : Nat → Tm Empty) : Prop :=
  ∀ i A, At Γ i A → evalTermWith markPairLet (θ i) env = some (env' i) ∧ startsLet (θ i) = false

local notation "RealizesOn" => RealizesOnWith markPairLet

theorem RealizesOnWith.lift {Γ : VCtx (Ty Empty)} {env env' : Env} {θ : Nat → Tm Empty}
    (h : RealizesOn Γ env env' θ) (A : Ty Empty) (v : Val) :
    RealizesOn (A :: Γ) (extend env v) (extend env' v) (Tm.liftSubst θ) := by
  intro i B hi
  cases i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i =>
    change evalTerm ((θ i).rename Nat.succ) (extend env v) = some (env' i) ∧
      startsLet ((θ i).rename Nat.succ) = false
    rw [evalTerm_rename _ (env := env) (ρ := Nat.succ) (fun _ => rfl)]
    rw [startsLet_rename]
    exact h i B hi

theorem evalTerm_substOn {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.HasType Γ t A) {env env' : Env} {θ : Nat → Tm Empty}
    (h : RealizesOn Γ env env' θ) : evalTerm (t.subst θ) env = evalTerm t env' := by
  induction ht generalizing env env' θ with
  | var hi => exact (h _ _ hi).1
  | @op _ _ f _ _ => exact f.elim
  | @let₁ _ a _ A _ _ _ ix it =>
    simp only [Tm.subst, evalTermWith, ix h]
    cases evalTerm a env' with
    | none => rfl
    | some v => exact it (h.lift A v)
  | @pair _ a b _ _ ha hb ix iy =>
    simp only [Tm.subst, evalTermWith, startsLet_substOn ha (fun i A hi => (h i A hi).2),
      startsLet_substOn hb (fun i A hi => (h i A hi).2), ix h, iy h]
  | unit => rfl
  | @let₂ _ a b A B _ _ _ ix it =>
    simp only [Tm.subst, evalTermWith, ix h]
    cases evalTerm a env' with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      exact it ((h.lift A _).lift B _)
  | inl _ it => simp only [Tm.subst, evalTermWith, it h]
  | inr _ it => simp only [Tm.subst, evalTermWith, it h]
  | @case _ a _ _ A B _ _ _ _ ix il ir =>
    simp only [Tm.subst, evalTermWith, ix h]
    cases evalTerm a env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift A _) | exact ir (h.lift B _)
  | abort => rfl

theorem evalRegion_substOn {Γ : VCtx (Ty Empty)} {r : Region Empty} {L : LCtx (Ty Empty)}
    (hr : HasType Γ r L) {env env' : Env} {θ : Nat → Tm Empty}
    (h : RealizesOn Γ env env' θ) : evalRegion (r.substVars θ) env = evalRegion r env' := by
  induction hr generalizing env env' θ with
  | br hi ht => simp only [substVars, evalRegionWith, evalTerm_substOn ht h]
  | @let₁ _ _ a _ A ht _ ih =>
    simp only [substVars, evalRegionWith, evalTerm_substOn ht h]
    cases evalTerm a env' with
    | none => rfl
    | some v => exact ih (h.lift A v)
  | @let₂ _ _ a _ A B ht _ ih =>
    simp only [substVars, evalRegionWith, evalTerm_substOn ht h]
    cases evalTerm a env' with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      exact ih ((h.lift A _).lift B _)
  | @case _ _ a _ _ A B ht _ _ il ir =>
    simp only [substVars, evalRegionWith, evalTerm_substOn ht h]
    cases evalTerm a env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift A _) | exact ir (h.lift B _)
  | cfg R _ _ ie ib =>
    simp only [substVars, evalRegionWith, ie h]
    congr 1
    funext i v
    exact ib i (h.lift (R i) v)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
