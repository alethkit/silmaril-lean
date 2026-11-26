module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Inner
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.GraphRelation
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

universe u w x

variable {Φ : Type u} {α : Type w} {σ : Type x}
  {instr : Φ → Value α → σ → Value α → σ → Prop}
  {faults : Φ → Value α → σ → σ → Prop} {prim : Φ → Value α → σ → Prop}
  {env : Env α} {body : Region Φ}

local notation "two" => followGraph instr faults prim env (fun _ : Fin 2 => body)
local notation "outer" => followGraph instr faults prim env (fun _ : Fin 1 => innerBlock body)
local notation "flat" => followGraph instr faults prim env (fun _ : Fin 1 => body.renameLabels Nat.pred)

private inductive FlatRel : Jump α σ → Jump α σ → Prop where
  | same (i : Nat) (a : Value α) (s : σ) : FlatRel ⟨i, a, s⟩ ⟨i.pred, a, s⟩

private theorem pred_internal (i : Nat) : i.pred < 1 ↔ i < 2 := by
  rw [Nat.pred_eq_sub_one]
  omega

private theorem pred_external (i : Nat) : 1 ≤ i.pred ↔ 2 ≤ i := by
  rw [Nat.pred_eq_sub_one]
  omega

private theorem pred_external_index (i : Nat) : i.pred - 1 = i - 2 := by
  rw [Nat.pred_eq_sub_one]
  omega

private theorem flat_matches : Matches (two : Graph (Jump α σ) (Exit α σ)) flat FlatRel where
  forward := by
    intro a b c related edge
    cases related with | same i a s =>
    obtain ⟨here, there, run⟩ := edge
    exact ⟨⟨c.label.pred, c.payload, c.state⟩,
      ⟨(pred_internal i).mpr here, (pred_internal c.label).mpr there, run.renameLabels Nat.pred⟩, by
      cases c; exact .same _ _ _⟩
  backward := by
    intro a b d related edge
    cases related with | same i a s =>
    obtain ⟨here, there, run⟩ := edge
    obtain ⟨j, same, run⟩ := Semantics.Region.Eval.of_renameLabels run
    exact ⟨⟨j, d.payload, d.state⟩,
      ⟨(pred_internal i).mp here, (pred_internal j).mp (same ▸ there), run⟩, by
      cases d
      dsimp at same
      subst same
      exact .same _ _ _⟩

private theorem flat_finish {a b : Jump α σ} (related : FlatRel a b) (o : Exit α σ) :
    (two).finish a o ↔ (flat).finish b o := by
  cases related with | same i a s =>
  cases o with
  | ret j v t =>
    constructor
    · rintro (⟨outside, same, rfl, rfl⟩ | ⟨here, run⟩)
      · exact .inl ⟨(pred_external i).mpr outside, (pred_external_index i).trans same, rfl, rfl⟩
      · have label : (2 + j).pred = 1 + j := by rw [Nat.pred_eq_sub_one]; omega
        exact .inr ⟨(pred_internal i).mpr here, label ▸ run.renameLabels Nat.pred⟩
    · rintro (⟨outside, same, rfl, rfl⟩ | ⟨here, run⟩)
      · exact .inl ⟨(pred_external i).mp outside, (pred_external_index i).symm.trans same, rfl, rfl⟩
      · obtain ⟨k, same, unshifted⟩ := Semantics.Region.Eval.of_renameLabels run
        have hk : k = 2 + j := by rw [Nat.pred_eq_sub_one] at same; omega
        exact .inr ⟨(pred_internal i).mp here, hk ▸ unshifted⟩
  | fault t =>
    constructor
    · rintro ⟨here, run⟩
      exact ⟨(pred_internal i).mpr here, run.renameLabels Nat.pred⟩
    · rintro ⟨here, run⟩
      exact ⟨(pred_internal i).mp here, run.of_renameLabels⟩
  | diverge =>
    constructor
    · rintro ⟨here, run⟩
      exact ⟨(pred_internal i).mpr here, (External.Diverges.renameLabels_iff Nat.pred).mpr run⟩
    · rintro ⟨here, run⟩
      exact ⟨(pred_internal i).mp here, (External.Diverges.renameLabels_iff Nat.pred).mp run⟩

private inductive OuterRel : Jump α σ → Jump α σ → Prop where
  | same (i : Nat) (a : Value α) (s : σ) : OuterRel ⟨i, a, s⟩ ⟨i + 1, a, s⟩

private theorem outside_reach {p q : Jump α σ} (outside : 2 ≤ p.label)
    (reach : ((two).inner inside).Reaches p q) : q = p := by
  induction reach using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head edge _ _ =>
    obtain ⟨⟨here, _, _⟩, _⟩ := edge
    omega

private theorem outside_ordinary {p : Jump α σ} (outside : 2 ≤ p.label) {o : Exit α σ} :
    ((two).inner inside).Ordinary p (.inr o) ↔ (two).finish p o := by
  rw [Graph.ordinary_close_iff]
  have safe : ¬ ((two).inner inside).ReachesUB p := by rintro ⟨_, _, no⟩; exact no
  rcases p with ⟨i, a, s⟩
  constructor
  · rintro ⟨_, ⟨q, reach, finish⟩ | ⟨_, path, start, step⟩⟩
    · rwa [outside_reach outside reach] at finish
    · have edge := step 0
      rw [start] at edge
      obtain ⟨⟨here, _, _⟩, _⟩ := edge
      omega
  · exact fun finish => ⟨safe, .inl ⟨_, .refl, finish⟩⟩

private theorem outer_matches : Matches (outer : Graph (Jump α σ) (Exit α σ)) ((two).outer inside) OuterRel where
  forward := by
    intro a b c related edge
    cases related with | same i a s =>
    obtain ⟨here, there, run⟩ := edge
    change i < 1 at here
    have hi : i = 0 := by omega
    have same : c.label = 0 := by omega
    subst i
    rcases c with ⟨j, v, t⟩
    change j = 0 at same
    subst j
    exact ⟨⟨1, v, t⟩, (inner_return_again (by decide)).mpr run, .same 0 v t⟩
  backward := by
    intro a b d related edge
    cases related with | same i a s =>
    have bound := Graph.outer_step_iff.mp edge
    obtain ⟨q, path, ⟨here, there, _⟩, notInner⟩ := bound.2
    by_cases hi : i = 0
    · subst i
      rcases d with ⟨j, v, t⟩
      change ¬ j = 0 at notInner
      change j < 2 at there
      have same : j = 1 := by omega
      subst j
      exact ⟨⟨0, v, t⟩, ⟨Nat.zero_lt_one, Nat.zero_lt_one, (inner_return_again (by decide)).mp edge⟩, .same 0 v t⟩
    · rw [outside_reach (by change 2 ≤ i + 1; omega) path] at here
      change i + 1 < 2 at here
      omega

private theorem outer_finish {a b : Jump α σ} (related : OuterRel a b) (o : Exit α σ) :
    (outer).finish a o ↔ ((two).outer inside).finish b o := by
  cases related with | same i a s =>
  cases i with
  | zero =>
    cases o with
    | ret j v t =>
      simpa [followGraph, Graph.outer, Nat.add_comm] using
        (inner_return_out (instr := instr) (env := env) (by decide : 1 < 2) j).symm
    | fault t =>
      simpa [followGraph, Graph.outer] using (inner_fault (instr := instr) (env := env) (by decide : 1 < 2)).symm
    | diverge =>
      simpa [followGraph, Graph.outer] using (inner_div (instr := instr) (env := env) (by decide : 1 < 2)).symm
  | succ i =>
    rw [show ((two).outer inside).finish ⟨i.succ + 1, a, s⟩ o =
        ((two).inner inside).Ordinary ⟨i.succ + 1, a, s⟩ (.inr o) from rfl,
      outside_ordinary (by change 2 ≤ i.succ + 1; omega)]
    cases o <;> simp [followGraph,
      show ¬ i.succ + 1 < 2 by omega, show 1 ≤ i.succ by omega,
      show 2 ≤ i.succ + 1 by omega, show i.succ - 1 = i.succ + 1 - 2 by omega]

private theorem staged_outcomes (q : Jump α σ) : ((two).outer inside).outcomes q = (two).outcomes q := by
  have h₁ : ¬ (two).ReachesUB q := by rintro ⟨_, _, no⟩; exact no
  have h₂ : ¬ ((two).outer inside).ReachesUB q :=
    fun top => h₁ (Graph.reachesUB_outer_iff.mp top)
  have same := Graph.close_outer (g := two) (inside := inside) (p := q)
  simpa only [Graph.close, ite_eq_right h₁, ite_eq_right h₂, WithTop.coe_inj] using same

/-- The staged and flattened dispatchers have the same ordinary outcome set
at each starting payload, measured in the native one-block label interface. -/
theorem staged_eq_flat (i : Nat) (a : Value α) (s : σ) (o : Exit α σ) :
    o ∈ (outer).outcomes ⟨i, a, s⟩ ↔ o ∈ (flat).outcomes ⟨i, a, s⟩ := by
  have step₁ := (outer_matches (instr := instr) (faults := faults) (prim := prim) (env := env) (body := body)).outcomes_iff
    (OuterRel.same i a s) rfl o (fun r => outer_finish r o)
  rw [staged_outcomes] at step₁
  have step₂ := (flat_matches (instr := instr) (faults := faults) (prim := prim) (env := env) (body := body)).outcomes_iff
    (FlatRel.same (i + 1) a s) rfl o (fun r => flat_finish r o)
  exact step₁.trans step₂

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
