module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Route
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Dispatch
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Substitution
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (liftLSubstVars liftLSubst liftLSubstN labelId)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops PureValue Realizes)
open Silmaril.DeBruijn (lift)

universe u v w x

variable {Φ : Type u} {α : Type w} {σ : Type x} {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- A forwarded exit retains the state reached by its producer. -/
abbrev exitRoute (instr : Φ → Value α → σ → Value α → σ → Prop)
    (env : Env α) (k : Nat → Region Φ) : Route α σ :=
  fun i a s j b => Semantics.Region.Eval instr (extend env a) (k i) s j b s

theorem lift_capture {instr : Φ → Value α → σ → Value α → σ → Prop} {env : Env α}
    {k : Nat → Region Φ} (v : Value α) (i : Nat) (a : Value α) (s : σ) (j : Nat) (b : Value α) :
    exitRoute instr (extend env v) (liftLSubstVars k) i a s j b ↔ exitRoute instr env k i a s j b :=
  Semantics.Region.Eval.renameVars_iff (ρ := lift Nat.succ) (fun i => by cases i <;> rfl)

theorem label_at_local (k : Nat → Region Φ) {n i : Nat} (hi : i < n) :
    liftLSubstN n k i = labelId i := by
  induction n generalizing i with
  | zero => exact (Nat.not_lt_zero _ hi).elim
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (liftLSubstN n k i).renameLabels Nat.succ = labelId (i + 1)
      rw [ih (Nat.lt_of_succ_lt_succ hi)]
      rfl

theorem label_at_exit (k : Nat → Region Φ) (n i : Nat) :
    liftLSubstN n k (n + i) = (k i).renameLabels (n + ·) := by
  induction n with
  | zero =>
    have shift : (fun j : Nat => 0 + j) = id := funext Nat.zero_add
    rw [shift, Region.renameLabels_id]
    simp only [liftLSubstN, Nat.zero_add]
  | succ n ih =>
    rw [Nat.succ_add]
    change (liftLSubstN n k (n + i)).renameLabels Nat.succ = _
    rw [ih, Region.renameLabels_comp]
    congr 1
    funext j
    exact (Nat.succ_add n j).symm

private theorem lift_labels {instr : Φ → Value α → σ → Value α → σ → Prop} {env : Env α}
    {k : Nat → Region Φ} (n i : Nat) (a : Value α) (s : σ) (j : Nat) (b : Value α) :
    exitRoute instr env (liftLSubstN n k) i a s j b ↔ (Route.under n (exitRoute instr env k)) i a s j b := by
  by_cases hi : i < n
  · rw [Route.under_in hi]
    change Semantics.Region.Eval instr (extend env a) (liftLSubstN n k i) s j b s ↔ _
    rw [label_at_local k hi]
    constructor
    · intro run; cases run with | br arg => cases arg; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact .br .var
  · rw [Route.under_out (Nat.le_of_not_lt hi)]
    change Semantics.Region.Eval instr (extend env a) (liftLSubstN n k i) s j b s ↔ _
    have idx : liftLSubstN n k i = (k (i - n)).renameLabels (n + ·) := by
      have h := label_at_exit k n (i - n)
      rwa [Nat.add_sub_of_le (Nat.le_of_not_lt hi)] at h
    rw [idx]
    exact ⟨Semantics.Region.Eval.of_renameLabels, fun ⟨j, same, run⟩ => same.symm ▸ run.renameLabels (n + ·)⟩

theorem guard_capture {Γ L K : List τ} {k : Nat → Region Φ}
    (h : Region.LSubst.Forwards Γ L K k) (D : τ) : Region.LSubst.Forwards (D :: Γ) L K (liftLSubstVars k) := by
  intro i A hi
  obtain ⟨j, b, B, eq, hj, hb⟩ := h hi
  refine ⟨j, b.rename (lift Nat.succ), B, by simp [liftLSubstVars, eq, Region.renameVars], hj, ?_⟩
  have typed := (Region.ValueBranches.br hj hb).renameVars ((Ren.wk Γ D).lift A)
  cases typed with
  | br label hb => exact (Option.some.inj (label.symm.trans hj)) ▸ hb

omit [HasTy Φ τ] in
private theorem guard_labels {Γ L K : List τ} {k : Nat → Region Φ}
    (h : Region.LSubst.Forwards Γ L K k) (R : List τ) :
    Region.LSubst.Forwards Γ (R ++ L) (R ++ K) (liftLSubstN R.length k) := by
  induction R with
  | nil => exact h
  | cons D R ih =>
    intro i A hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact ⟨0, .var 0, D, rfl, rfl, .var rfl⟩
    | succ i =>
      obtain ⟨j, b, B, eq, hj, hb⟩ := ih hi
      exact ⟨j + 1, b, B, by simp [liftLSubstN, liftLSubst, eq, Region.renameLabels], hj, hb⟩

private theorem br_forward {O : Ops Φ α σ} {env : Env α} {l j : Nat} {a b : Tm Φ}
    {source target : Value α} {k : Nat → Region Φ}
    (sourcePure : PureValue O env a source) (targetPure : PureValue O (extend env source) b target)
    (eq : k l = .br j b) :
    Routed O env (.br l a) ((.br l a : Region Φ).lsubst k) (exitRoute O.instr env k) := by
  have sim := (Realizes.single sourcePure).region (k l)
  refine ⟨?_, ?_, ?_⟩
  · intro s label value t
    constructor
    · intro run
      have finish := sim.eval.mp run
      have sameState : t = s := by
        rw [eq] at finish
        cases finish with | br arg => exact (targetPure.unique arg).2
      subst t
      exact ⟨l, source, .br (sourcePure.eval s), finish⟩
    · rintro ⟨i, v, head, tail⟩
      cases head with
      | br arg =>
        obtain ⟨rfl, rfl⟩ := sourcePure.unique arg
        exact sim.eval.mpr tail
  · intro s t
    constructor
    · intro run
      have mid := sim.fault.mp run
      rw [eq] at mid
      cases mid with | br arg => exact (targetPure.noFault arg).elim
    · intro run
      cases run with | br arg => exact (sourcePure.noFault arg).elim
  · intro s
    constructor
    · intro run
      have mid := sim.div.mp run
      rw [eq] at mid
      cases mid.unfold with
      | core h => cases h
      | br arg => exact (targetPure.noDiv arg).elim
    · intro run
      cases run.unfold with
      | core h => cases h
      | br arg => exact (sourcePure.noDiv arg).elim

/-- Interpret whole guarded literal forwarding. Nested CFGs keep their own
local dispatchers and forward only exits from the enclosing interface. -/
theorem forwarding {Γ L K : List τ} {r : Region Φ} (hr : Region.ValueBranches Γ r L)
    {k : Nat → Region Φ} (hk : Region.LSubst.Forwards Γ L K k) (O : Ops Φ α σ) (env : Env α) :
    Routed O env r (r.lsubst k) (exitRoute O.instr env k) := by
  induction hr generalizing env K k with
  | br hl ha =>
    obtain ⟨j, b, B, eq, _, hb⟩ := hk hl
    obtain ⟨source, hsource⟩ := PureValue.ofBranchValue (O := O) (env := env) ha
    obtain ⟨_, htarget⟩ := PureValue.ofBranchValue (O := O) (env := extend env source) hb
    exact br_forward hsource htarget eq
  | let₁ ha _ ih =>
    exact Routed.let₁ fun v => (ih (guard_capture hk _) (extend env v)).congr_route (lift_capture v)
  | let₂ ha _ ih =>
    apply Routed.let₂
    intro a b
    have h := ih (guard_capture (guard_capture hk _) _) (extend (extend env a) b)
    exact (h.congr_route (lift_capture b)).congr_route (lift_capture a)
  | case ha _ _ il ir =>
    exact Routed.case
      (fun v => (il (guard_capture hk _) (extend env v)).congr_route (lift_capture v))
      (fun v => (ir (guard_capture hk _) (extend env v)).congr_route (lift_capture v))
  | @cfg n Γ e L bs R he hb ie ib =>
    have lifted := guard_labels hk (List.ofFn R)
    simp only [List.length_ofFn] at lifted
    apply Routed.cfg _ ((ie lifted env).congr_route (lift_labels n))
    intro i v
    have h := ib i (guard_capture lifted _) (extend env v)
    exact (h.congr_route (lift_capture v)).congr_route (lift_labels n)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity
