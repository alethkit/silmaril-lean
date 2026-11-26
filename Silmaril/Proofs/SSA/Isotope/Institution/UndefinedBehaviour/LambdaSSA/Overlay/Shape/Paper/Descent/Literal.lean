module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Dispatch
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Forwarding
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Substitution
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (liftLSubstVars liftLSubstN)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops RegionAt PureValue Realizes)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity (label_at_local label_at_exit)

universe u v w x

variable {Φ : Type u} {α : Type w} {σ : Type x} {O : Ops Φ α σ} {env env' : Env α}

@[expose] def Exit.rename (ρ : Nat → Nat) : Exit α σ → Exit α σ
  | .ret j a t => .ret (ρ j) a t
  | .fault t => .fault t
  | .diverge => .diverge

theorem runs_renameLabels (r : Region Φ) (ρ : Nat → Nat) (s : σ) (o : Exit α σ) :
    Runs O env (r.renameLabels ρ) s o ↔ ∃ e, Exit.rename ρ e = o ∧ Runs O env r s e := by
  cases o with
  | ret j a t =>
    constructor
    · intro run
      obtain ⟨i, eq, original⟩ := Semantics.Region.Eval.of_renameLabels run
      exact ⟨.ret i a t, congrArg (fun l => Exit.ret l a t) eq.symm, original⟩
    · rintro ⟨e, eq, run⟩
      cases e with
      | ret i v m => exact eq ▸ (show Runs O env (r.renameLabels ρ) s (.ret (ρ i) v m) from
          run.renameLabels ρ)
      | fault | diverge => cases eq
  | fault t =>
    rw [show Runs O env (r.renameLabels ρ) s (.fault t) ↔ Runs O env r s (.fault t) from
      Semantics.Region.Fault.renameLabels_iff ρ]
    constructor
    · exact fun run => ⟨.fault t, rfl, run⟩
    · rintro ⟨e, eq, run⟩
      cases e with
      | fault t' => exact (Exit.fault.inj eq) ▸ run
      | ret | diverge => cases eq
  | diverge =>
    rw [show Runs O env (r.renameLabels ρ) s .diverge ↔ Runs O env r s .diverge from
      External.Diverges.renameLabels_iff ρ]
    constructor
    · exact fun run => ⟨.diverge, rfl, run⟩
    · rintro ⟨e, eq, run⟩
      cases e with
      | diverge => exact run
      | ret | fault => cases eq

theorem vars (r : Region Φ) {ρ : Nat → Nat} (agree : ∀ i, env' (ρ i) = env i) :
    RegionAt O env' (r.renameVars ρ) env r :=
  ⟨Semantics.Region.Eval.renameVars_iff agree, Semantics.Region.Fault.renameVars_iff agree,
    External.Diverges.renameVars_iff agree⟩

abbrev continuation (O : Ops Φ α σ) (env : Env α) (k : Nat → Region Φ) : Post α σ :=
  fun p o => Runs O (extend env p.payload) (k p.label) p.state o

private theorem capture (v : Value α) (k : Nat → Region Φ) (p : Jump α σ) (o : Exit α σ) :
    continuation O (extend env v) (liftLSubstVars k) p o ↔ continuation O env k p o :=
  regionAt_iff.mp (vars (k p.label) (ρ := lift Nat.succ) (fun i => by cases i <;> rfl)) _ _

private theorem labels (k : Nat → Region Φ) (n : Nat) (p : Jump α σ) (o : Exit α σ) :
    continuation O env (liftLSubstN n k) p o ↔ (continuation O env k).under n p o := by
  unfold continuation Post.under
  by_cases hi : p.label < n
  · rw [ite_eq_left hi, label_at_local k hi]
    constructor
    · intro run
      cases o with
      | ret => cases run with | br arg => cases arg; rfl
      | fault => cases run with | br arg => cases arg
      | diverge =>
        cases (show External.Diverges O.instr O.prim _ from run).unfold with
        | br arg => cases arg
        | core step => cases step
    · rintro rfl
      exact Semantics.Region.Eval.br .var
  · have index : liftLSubstN n k p.label = (k (p.label - n)).renameLabels (n + ·) := by
      have h := label_at_exit k n (p.label - n)
      rwa [Nat.add_sub_of_le (Nat.le_of_not_lt hi)] at h
    rw [ite_eq_right hi, index, runs_renameLabels]
    apply exists_congr
    intro e
    have same : Exit.rename (n + ·) e = Exit.shift n e := by cases e <;> rfl
    rw [same, eq_comm (a := Exit.shift n e)]

private theorem branch {a : Tm Φ} {v : Value α} {i : Nat} (pure : PureValue O env a v)
    (k : Nat → Region Φ) : Sequenced O env (.br i a) ((.br i a : Region Φ).lsubst k) (continuation O env k) := by
  intro s o
  rw [show (.br i a : Region Φ).lsubst k = (k i).substVars (Tm.singleSubst a) from rfl,
    regionAt_iff.mp ((Realizes.single pure).region (k i)) s o]
  constructor
  · exact fun run => ⟨.ret i v s, Semantics.Region.Eval.br (pure.eval s), run⟩
  · rintro ⟨e, run, post⟩
    cases e with
    | ret j b t =>
      cases run with
      | br arg => obtain ⟨rfl, rfl⟩ := pure.unique arg; exact post
    | fault => cases run with | br arg => exact (pure.noFault arg).elim
    | diverge =>
      cases (show External.Diverges O.instr O.prim _ from run).unfold with
      | br arg => exact (pure.noDiv arg).elim
      | core step => cases step

/-- Execute the guarded producer up to its first external outcome. Its
successful payload and final state start the chosen continuation. -/
theorem literal {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ L : List τ} {r : Region Φ}
    (h : Region.ValueBranches Γ r L) (k : Nat → Region Φ) :
    Sequenced O env r (r.lsubst k) (continuation O env k) := by
  induction h generalizing env k with
  | br _ ha =>
    obtain ⟨v, pure⟩ := PureValue.ofBranchValue (O := O) (env := env) ha
    exact branch pure k
  | let₁ _ _ ih =>
    exact Sequenced.let₁ fun v => (ih (k := liftLSubstVars k)).congr (capture v k)
  | let₂ _ _ ih =>
    exact Sequenced.let₂ fun v w =>
      ((ih (k := liftLSubstVars (liftLSubstVars k))).congr (capture w (liftLSubstVars k))).congr (capture v k)
  | case _ _ _ il ir =>
    exact Sequenced.case
      (fun v => (il (k := liftLSubstVars k)).congr (capture v k))
      (fun v => (ir (k := liftLSubstVars k)).congr (capture v k))
  | @cfg n Γ e L bs R he hb ie ib =>
    exact Sequenced.cfg ((ie (k := liftLSubstN n k)).congr (labels k n))
      (fun i v => ((ib i (k := liftLSubstVars (liftLSubstN n k))).congr (capture v _)).congr (labels k n))

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent
