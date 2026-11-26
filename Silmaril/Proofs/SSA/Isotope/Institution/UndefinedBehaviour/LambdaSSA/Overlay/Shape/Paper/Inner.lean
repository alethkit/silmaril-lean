module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.FollowGraph
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Codiagonal.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.GraphRelation
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open Silmaril.DeBruijn (lift)
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback
open Silmaril.Isotope.LambdaSSA.Region.CfgEta (singleCfg)

universe u w x

variable {Φ : Type u} {α : Type w} {σ : Type x}
  {instr : Φ → Value α → σ → Value α → σ → Prop}
  {faults : Φ → Value α → σ → σ → Prop} {prim : Φ → Value α → σ → Prop}
  {env : Env α} {body : Region Φ}

abbrev innerBlock (body : Region Φ) : Region Φ :=
  singleCfg (.br 0 (.var 0)) (body.renameVars (lift Nat.succ))

private theorem extra_capture (env : Env α) (a v : Value α) (i : Nat) :
    extend (extend env a) v (lift Nat.succ i) = extend env v i := by
  cases i <;> rfl

theorem innerBlock_eval {s t : σ} {a v : Value α} {j : Nat} :
    Semantics.Region.Eval instr (extend env a) (innerBlock body) s j v t ↔
      Semantics.Region.Follow instr env (fun _ : Fin 1 => body) 0 a s j v t := by
  constructor
  · intro run
    cases run with
    | cfg head tail =>
      cases head with
      | br head =>
        cases head
        exact tail.map_block (fun _ cur {_ _ _ _} run => Semantics.Region.Eval.of_renameVars (extra_capture env a cur) run)
  · intro tail
    exact .cfg (.br .var) (tail.map_block (fun _ cur {_ _ _ _} run =>
      run.renameVars (extra_capture env a cur)))

theorem innerBlock_fault {s t : σ} {a : Value α} :
    Semantics.Region.Fault instr faults (extend env a) (innerBlock body) s t ↔
      Semantics.Region.FollowFault instr faults env (fun _ : Fin 1 => body) 0 a s t := by
  constructor
  · intro run
    cases run with
    | cfg_entry head => cases head with | br head => cases head
    | cfg_follow head tail =>
      cases head with
      | br head =>
        cases head
        exact tail.map_block (fun _ cur {_ _ _ _} run => Semantics.Region.Eval.of_renameVars (extra_capture env a cur) run)
          (fun _ cur {_ _} run => run.of_renameVars (extra_capture env a cur))
  · intro tail
    exact .cfg_follow (.br .var) (tail.map_block (fun _ cur {_ _ _ _} run => run.renameVars (extra_capture env a cur))
      (fun _ cur {_ _} run => run.renameVars (extra_capture env a cur)))

theorem innerBlock_div {s : σ} {a : Value α} :
    External.Diverges instr prim (.region (extend env a) (innerBlock body) s) ↔
      External.Diverges instr prim (.follow env (fun _ : Fin 1 => body) 0 a s) := by
  have renamed : Config.VarRenaming
      (.follow env (fun _ : Fin 1 => body) 0 a s)
      (.follow (extend env a) (fun _ : Fin 1 => body.renameVars (lift Nat.succ)) 0 a s) :=
    .follow (ρ := Nat.succ) (fun _ => rfl)
  constructor
  · intro run
    cases run.unfold with
    | core step =>
      cases step with
      | cfg_entry head =>
        cases head.unfold with
        | core step => cases step
        | br head => cases head
      | cfg_follow head tail =>
        cases head with
        | br head =>
          cases head
          exact tail.of_varRenaming_rev renamed
  · intro tail
    exact .fold_core (.cfg_follow (.br .var) (tail.of_varRenaming renamed))

@[expose] def inside (q : Jump α σ) : Prop := q.label = 0

local notation "one" => followGraph instr faults prim env (fun _ : Fin 1 => body)
local notation "two" => followGraph instr faults prim env (fun _ : Fin 2 => body)

private inductive InnerRel : Jump α σ → Jump α σ → Prop where
  | same {i : Nat} {a : Value α} {s : σ} (hi : i < 2) : InnerRel ⟨0, a, s⟩ ⟨i, a, s⟩

private theorem inner_matches :
    Matches (one : Graph (Jump α σ) (Exit α σ)) ((two).inner inside) InnerRel where
  forward := by
    intro a b c rel edge
    cases rel
    obtain ⟨_, cj, run⟩ := edge
    have same : c.label = 0 := by omega
    rcases c with ⟨j, v, t⟩
    change j = 0 at same
    subst j
    exact ⟨⟨0, v, t⟩, ⟨⟨‹_ < 2›, Nat.zero_lt_succ _, run⟩, rfl⟩, .same (by decide)⟩
  backward := by
    intro a b d rel edge
    cases rel
    obtain ⟨⟨_, _, run⟩, same⟩ := edge
    rcases d with ⟨j, v, t⟩
    change j = 0 at same
    subst j
    exact ⟨⟨0, v, t⟩, ⟨Nat.zero_lt_one, Nat.zero_lt_one, run⟩, .same (by decide)⟩

theorem inner_return_again {a b : Value α} {s t : σ} {i : Nat} (hi : i < 2) :
    ((two).inner inside).Ordinary ⟨i, a, s⟩ (.inl ⟨1, b, t⟩) ↔
      Semantics.Region.Eval instr (extend env a) (innerBlock body) s 0 b t := by
  rw [innerBlock_eval, ← follow_ret (p := ⟨0, a, s⟩) (faults := faults) (prim := prim), Graph.ordinary_close_iff]
  have finite := (inner_matches (instr := instr) (faults := faults) (prim := prim) (env := env) (body := body)).finite_iff
    (o := .ret 0 b t) (o' := .inl ⟨1, b, t⟩) ?_ (InnerRel.same hi (a := a) (s := s))
  · simpa [Graph.ReachesUB, Graph.outcomes, Graph.inner, followGraph] using finite.symm
  · intro p q rel
    cases rel with
    | same insideBlock =>
      simp [followGraph, Graph.inner, inside, insideBlock]

theorem inner_return_out {a b : Value α} {s t : σ} {i : Nat} (hi : i < 2) (j : Nat) :
    ((two).inner inside).Ordinary ⟨i, a, s⟩ (.inr (.ret j b t)) ↔
      Semantics.Region.Eval instr (extend env a) (innerBlock body) s (j + 1) b t := by
  rw [innerBlock_eval, ← follow_ret (p := ⟨0, a, s⟩) (faults := faults) (prim := prim), Graph.ordinary_close_iff]
  have finite := (inner_matches (instr := instr) (faults := faults) (prim := prim) (env := env) (body := body)).finite_iff
    (o := .ret (j + 1) b t) (o' := .inr (.ret j b t)) ?_ (InnerRel.same hi (a := a) (s := s))
  · simpa [Graph.ReachesUB, Graph.outcomes, Graph.inner, followGraph] using finite.symm
  · intro p q rel
    cases rel with
    | same insideBlock =>
      have out : ¬ 2 ≤ _ := Nat.not_le_of_lt insideBlock
      simp [followGraph, Graph.inner, insideBlock, out, Nat.add_comm, Nat.add_left_comm]

theorem inner_fault {a : Value α} {s t : σ} {i : Nat} (hi : i < 2) :
    ((two).inner inside).Ordinary ⟨i, a, s⟩ (.inr (.fault t)) ↔
      Semantics.Region.Fault instr faults (extend env a) (innerBlock body) s t := by
  rw [innerBlock_fault, ← follow_fault (p := ⟨0, a, s⟩) (prim := prim), Graph.ordinary_close_iff]
  have finite := (inner_matches (instr := instr) (faults := faults) (prim := prim) (env := env) (body := body)).finite_iff
    (o := .fault t) (o' := .inr (.fault t)) ?_ (InnerRel.same hi (a := a) (s := s))
  · simpa [Graph.ReachesUB, Graph.outcomes, Graph.inner, followGraph] using finite.symm
  · intro p q rel
    cases rel with
    | same insideBlock => simp [followGraph, Graph.inner, insideBlock]

theorem inner_div {a : Value α} {s : σ} {i : Nat} (hi : i < 2) :
    ((two).inner inside).Ordinary ⟨i, a, s⟩ (.inr .diverge) ↔
      External.Diverges instr prim (.region (extend env a) (innerBlock body) s) := by
  rw [innerBlock_div, ← follow_div (p := ⟨0, a, s⟩) (faults := faults), Graph.ordinary_close_iff]
  have transport := inner_matches (instr := instr) (faults := faults) (prim := prim) (env := env) (body := body)
  have rel := InnerRel.same hi (a := a) (s := s)
  have finite := transport.finite_iff (o := .diverge) (o' := .inr .diverge) ?_ rel
  · simpa [Graph.ReachesUB, Graph.outcomes, Graph.inner, followGraph] using
      (or_congr finite (transport.infinite_iff rel)).symm
  · intro p q rel
    cases rel with
    | same insideBlock => simp [followGraph, Graph.inner, insideBlock]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
