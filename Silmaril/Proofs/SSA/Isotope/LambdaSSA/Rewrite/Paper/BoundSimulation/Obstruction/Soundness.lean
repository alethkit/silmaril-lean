module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.CfgEta
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Feedback
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms

/-! # Preservation by every default Paper equation

The simulation case uses totality of constructor values. The proof also
covers both substitution congruences, the product equations and duplicate
feedback collapse.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction

theorem observes_collapse {e p : Region Empty} (env : Env) :
    evalRegion (CfgEta.Codiagonal.nested e p) env =
      evalRegion (CfgEta.Codiagonal.flattened e p) env := by
  dsimp only [CfgEta.Codiagonal.nested, CfgEta.Codiagonal.flattened, CfgEta.singleCfg, evalRegion]
  simp only [evalRegion_renameLabels]
  change _ = one (mergeFeedback ∘ fun v => evalRegion p (extend env v)) (evalRegion e env)
  rw [← one_codiagonal]
  congr 1
  funext i v
  change one (fun w => evalRegion (p.renameVars (lift Nat.succ)) (extend (extend env v) w)) (.jump 0 v) =
    one (fun w => evalRegion p (extend env w)) (.jump 0 v)
  congr 1
  funext w
  exact evalRegion_renameVars p (extend_rename (ρ := Nat.succ) (fun _ => rfl) w)


theorem mapOut_localMap {Γ : VCtx (Ty Empty)} {A D : Ty Empty} {a : Tm Empty}
    (ha : Tm.BranchValue (A :: Γ) a D) {env : Env} (he : EnvTy Γ env)
    {L : LCtx (Ty Empty)} {x : Result} (ht : ResultTy (A :: L) x) :
    mapOut (fun i v => evalRegion (CfgEta.Uniformity.localMap a i) (extend env v)) x =
      onState (fun v => (evalTerm a (extend env v)).getD .unit) x := by
  cases x with
  | fault => rfl
  | diverges => rfl
  | jump i v =>
    cases i with
    | succ i => rfl
    | zero =>
      obtain ⟨T, hi, hv⟩ := ht
      cases Option.some.inj hi
      obtain ⟨w, hw, _⟩ := evalValue ha (he.extend hv)
      simp only [mapOut, CfgEta.Uniformity.localMap, evalRegion, hw, onState, Option.getD_some]

theorem observes_uniform {Γ L : List (Ty Empty)} {A D : Ty Empty}
    {e p q : Region Empty} {a : Tm Empty}
    (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L))
    (ha : Tm.BranchValue (A :: Γ) a D)
    (square : Same (A :: Γ)
      (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a)))
      ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => q)))) :
    Same Γ (CfgEta.singleCfg e p) (CfgEta.singleCfg (e.lsubst (CfgEta.Uniformity.localMap a)) q) := by
  intro env henv
  let f := fun v => (evalTerm a (extend env v)).getD .unit
  let body := fun v => evalRegion p (extend env v)
  let body' := fun v => evalRegion q (extend env v)
  let start := evalRegion e env
  change one body start = one body' (evalRegion (e.lsubst (CfgEta.Uniformity.localMap a)) env)
  rw [evalRegion_lsubst he henv, mapOut_localMap ha henv (evalRegion_typed he.hasType henv)]
  have good {x : Result} (hx : ResultTy (A :: L) x) (v : Val) (eq : x = .jump 0 v) : ValTy v A := by
    rw [eq] at hx
    obtain ⟨T, hi, hv⟩ := hx
    cases Option.some.inj hi
    exact hv
  have stable (v w : Val) (hv : ValTy v A) (eq : body v = .jump 0 w) : ValTy w A :=
    good (evalRegion_typed hp.hasType (henv.extend hv)) w eq
  have comm (v : Val) (hv : ValTy v A) : body' (f v) = onState f (body v) := by
    have h := square _ (henv.extend hv)
    have branch : ValueBranches (A :: Γ) (Region.br 0 a) (D :: L) := .br (ℓ := 0) rfl ha
    have lhs : evalRegion (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a))) (extend env v) =
        onState f (body v) := by
      rw [evalRegion_lsubst hp (henv.extend hv)]
      simp only [eval_liftLSubstVars]
      exact mapOut_localMap ha henv (evalRegion_typed hp.hasType (henv.extend hv))
    rw [lhs, evalRegion_lsubst branch (henv.extend hv)] at h
    obtain ⟨w, hw, _⟩ := evalValue ha (henv.extend hv)
    simp only [evalRegion, hw, mapOut, eval_liftLSubstVars] at h
    simpa only [f, hw, Option.getD_some] using h.symm
  apply one_eq_of_runs
  intro r _
  exact run_simulation stable comm (good (evalRegion_typed he.hasType henv))


theorem paper_same {Γ L : List (Ty Empty)} {r s : Region Empty}
    (h : Paper.Eqv Γ r s L) : Same Γ r s := by
  induction h with
  | cfgEta h => exact cfgEta_same h
  | productBeta h =>
    cases h with
    | @let₂Beta a _ b _ _ _ ha hb hr =>
      intro env henv
      obtain ⟨v, ev, _⟩ := evalValue ha henv
      obtain ⟨w, ew, _⟩ := evalValue hb henv
      have realized : Realizes env (extend (extend env v) w) (Tm.consSubst b (Tm.singleSubst a)) := by
        intro i
        cases i with
        | zero => exact ew
        | succ i => exact Realizes.single ev i
      simp only [evalRegion, evalTerm, ev, ew, pure]
      exact (evalRegion_subst _ realized).symm
  | productEta h =>
    cases h with
    | @let₂Eta _ i ℓ A B hi hℓ =>
      intro env henv
      have hv := henv hi
      cases eq : env i with
      | pair a b => simp [evalRegion, evalTerm, eq, extend]
      | atom x => exact x.elim
      | unit => rw [eq] at hv; cases hv
      | inl x => rw [eq] at hv; cases hv
      | inr x => rw [eq] at hv; cases hv
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact Same.case ht il ir
  | cfg R he hb ie ib => exact Same.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | lsubstCongr hp h ih =>
    intro env he
    rw [evalRegion_lsubst hp he, evalRegion_lsubst hp he]
    exact mapOut_congr (evalRegion_typed hp.hasType he) (fun i A hi v hv =>
      ih hi _ (he.extend hv))
  | lsubstPost h hr hs hσ ih =>
    intro env he
    rw [evalRegion_lsubst hr he, evalRegion_lsubst hs he, ih env he]
  | @substVars G r s L D θ h hθ ih =>
    intro env he
    let env' := fun i => (evalTerm (θ i) env).getD .unit
    have ht (i : Nat) (A : Ty Empty) (hi : At G i A) :
        evalTerm (θ i) env = some (env' i) ∧ ValTy (env' i) A := by
      obtain ⟨v, eq, hv⟩ := evalValue (hθ hi) he
      simpa [env', eq] using hv
    rw [evalRegion_substOn h.typed.1 (fun i A hi => (ht i A hi).1),
        evalRegion_substOn h.typed.2 (fun i A hi => (ht i A hi).1)]
    exact ih env' (fun {i A} hi => (ht i A hi).2)
  | renameLabels h hρ ih =>
    intro env he
    rw [evalRegion_renameLabels, evalRegion_renameLabels, ih env he]
  | @collapsePost Γ e A L p K σ he hp hσ =>
    intro env henv
    have hn : ValueBranches Γ (CfgEta.Codiagonal.nested e p) L :=
      .cfg (fun _ : Fin 1 => A) he (fun _ =>
        .cfg (fun _ : Fin 1 => A) (.br (ℓ := 0) rfl (.var (i := 0) rfl))
          (fun _ => hp.renameVars ((Ren.wk Γ A).lift A)))
    have hb : ValueBranches (A :: Γ) (p.renameLabels Nat.pred) (A :: L) := by
      rw [renameLabels_eq_lsubst]
      exact hp.lsubst (fun i _ hi =>
        .br (ℓ := i.pred) (CfgEta.Codiagonal.mergeLabels A L hi) (.var rfl))
    have hf : ValueBranches Γ (CfgEta.Codiagonal.flattened e p) L :=
      .cfg (fun _ : Fin 1 => A) he (fun _ => hb)
    rw [evalRegion_lsubst hn henv, evalRegion_lsubst hf henv, observes_collapse]
  | uniform he hp hq ha square ih => exact observes_uniform he hp ha ih

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
