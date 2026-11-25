module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CollapseObstruction.Evaluation

/-! # Exit substitution preserves local divergence observations -/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction

theorem mapOut_liftN (n : Nat) (ρ : Nat → Nat) (r : Result) :
    mapOut (fun i v => .jump (liftN n ρ i) v) r =
      insideMap n (fun i v => .jump (ρ i) v) r := by
  cases r with
  | jump i v =>
    by_cases h : i < n
    · simp [mapOut, insideMap, h, Silmaril.DeBruijn.liftN_lt ρ h]
    · simp [mapOut, insideMap, shiftOut, h, Silmaril.DeBruijn.liftN_ge ρ (Nat.le_of_not_gt h)]
  | diverges _ => rfl
  | fault => rfl

theorem evalRegion_renameLabels (r : Region Empty) (ρ : Nat → Nat) (env : Env) :
    evalRegion (r.renameLabels ρ) env = mapOut (fun i v => .jump (ρ i) v) (evalRegion r env) := by
  induction r generalizing ρ env with
  | br i t =>
    simp only [renameLabels, evalRegion]
    cases evalTerm t env <;> rfl
  | let₁ t r ih =>
    simp only [renameLabels, evalRegion]
    cases evalTerm t env with
    | none => rfl
    | some v => exact ih ρ _
  | let₂ t r ih =>
    simp only [renameLabels, evalRegion]
    cases evalTerm t env with
    | none => rfl
    | some v => cases v <;> first | rfl | exact ih ρ _
  | case t l r ihl ihr =>
    simp only [renameLabels, evalRegion]
    cases evalTerm t env with
    | none => rfl
    | some v => cases v <;> first | rfl | exact ihl ρ _ | exact ihr ρ _
  | cfg entry n bs ihe ihb =>
    simp only [renameLabels, evalRegion, ihe, ihb, mapOut_liftN]
    exact cfgRun_mapOut n _ _ _

theorem eval_liftLSubstVars (σ : Nat → Region Empty) (i : Nat) (env : Env) (u v : Val) :
    evalRegion (liftLSubstVars σ i) (extend (extend env u) v) = evalRegion (σ i) (extend env v) :=
  evalRegion_renameVars (σ i) (ρ := lift Nat.succ)
    (extend_rename (env := env) (env' := extend env u) (ρ := Nat.succ) (fun _ => rfl) v)

theorem liftLSubstN_local (n : Nat) (σ : Nat → Region Empty) {i : Nat} (hi : i < n) :
    liftLSubstN n σ i = labelId i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (liftLSubstN n σ i).renameLabels Nat.succ = _
      rw [ih (Nat.lt_of_succ_lt_succ hi)]
      rfl

theorem liftLSubstN_out (n : Nat) (σ : Nat → Region Empty) (i : Nat) :
    liftLSubstN n σ (n + i) = (σ i).renameLabels (n + ·) := by
  induction n with
  | zero =>
    rw [liftLSubstN, Nat.zero_add, show (fun j : Nat => 0 + j) = id from funext Nat.zero_add, renameLabels_id]
  | succ n ih =>
    rw [Nat.succ_add]
    change (liftLSubstN n σ (n + i)).renameLabels Nat.succ = _
    rw [ih, renameLabels_comp]
    congr 1
    funext j
    change Nat.succ (n + j) = n + 1 + j
    omega

theorem mapOut_liftLSubstN (n : Nat) (σ : Nat → Region Empty) (env : Env) (r : Result) :
    mapOut (fun i v => evalRegion (liftLSubstN n σ i) (extend env v)) r =
      insideMap n (fun i v => evalRegion (σ i) (extend env v)) r := by
  cases r with
  | jump i v =>
    change evalRegion (liftLSubstN n σ i) (extend env v) =
      (if i < n then .jump i v else shiftOut n (evalRegion (σ (i - n)) (extend env v)))
    by_cases h : i < n
    · rw [ite_eq_left h, liftLSubstN_local n σ h]
      rfl
    · rw [ite_eq_right h]
      have he : liftLSubstN n σ i = (σ (i - n)).renameLabels (n + ·) := by
        have eq := liftLSubstN_out n σ (i - n)
        rwa [Nat.add_sub_of_le (Nat.le_of_not_gt h)] at eq
      rw [he, evalRegion_renameLabels]
      rfl
  | diverges _ => rfl
  | fault => rfl

theorem evalRegion_lsubst {Γ : VCtx (Ty Empty)} {r : Region Empty} {L : LCtx (Ty Empty)}
    (hr : HasType Γ r L) {env : Env} (h : EnvTy Γ env) (σ : Nat → Region Empty) :
    evalRegion (r.lsubst σ) env = mapOut (fun i v => evalRegion (σ i) (extend env v)) (evalRegion r env) := by
  induction hr generalizing env σ with
  | br hi ht =>
    obtain ⟨v, eq, hv⟩ := evalTerm_typed ht h
    rw [lsubst, evalRegion_subst _ (Realizes.single eq), evalRegion, eq]
    rfl
  | let₁ ht _ ih =>
    obtain ⟨v, eq, hv⟩ := evalTerm_typed ht h
    simp only [lsubst, evalRegion, eq]
    rw [ih (h.extend hv)]
    congr 1
    funext i w
    exact eval_liftLSubstVars σ i env v w
  | let₂ ht _ ih =>
    obtain ⟨v, eq, hv⟩ := evalTerm_typed ht h
    cases hv with
    | pair h₁ h₂ =>
      simp only [lsubst, evalRegion, eq]
      rw [ih ((h.extend h₁).extend h₂)]
      congr 1
      funext i w
      rw [eval_liftLSubstVars, eval_liftLSubstVars]
  | case ht _ _ il ir =>
    obtain ⟨v, eq, hv⟩ := evalTerm_typed ht h
    cases hv with
    | inl hv =>
      simp only [lsubst, evalRegion, eq]
      rw [il (h.extend hv)]
      congr 1
      funext i w
      exact eval_liftLSubstVars σ i env _ w
    | inr hv =>
      simp only [lsubst, evalRegion, eq]
      rw [ir (h.extend hv)]
      congr 1
      funext i w
      exact eval_liftLSubstVars σ i env _ w
  | @cfg Δ K e n bs R he hb ihe ihb =>
    let k := fun i v => evalRegion (σ i) (extend env v)
    let d := fun i v => evalRegion (bs i) (extend env v)
    let d' := fun i v =>
      evalRegion ((bs i).lsubst (liftLSubstVars (liftLSubstN n σ))) (extend env v)
    let start := evalRegion e env
    have hd (i : Fin n) (v : Val) (hv : ValTy v (R i)) : d' i v = insideMap n k (d i v) := by
      change evalRegion ((bs i).lsubst _) (extend env v) = _
      rw [ihb i (h.extend hv)]
      simp only [eval_liftLSubstVars, mapOut_liftLSubstN, k, d]
    have hc (s : Frame n) (hs : FrameTy R K s) :
        step d' (mapTerminal (mapOut k) s) = mapTerminal (mapOut k) (step d s) := by
      cases s with
      | inl r => rfl
      | inr s =>
        obtain ⟨i, v⟩ := s
        change enter n (d' i v) = mapTerminal (mapOut k) (enter n (d i v))
        rw [hd i v hs, enter_insideMap]
    change finish d' (enter n (evalRegion (e.lsubst (liftLSubstN n σ)) env)) =
      mapOut k (finish d (enter n start))
    rw [ihe h, mapOut_liftLSubstN, enter_insideMap]
    exact finish_mapTerminalOn d d' (mapOut k) (fun _ => rfl) (FrameTy R K)
      (step_typed R K (fun i _ hv => evalRegion_typed (hb i) (h.extend hv)))
      hc (enter n start) (enter_typed R (evalRegion_typed he h))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence
