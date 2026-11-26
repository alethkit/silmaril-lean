module

public import Silmaril.SSA.Peggy.Optimizer.Extension.Defs

public section

namespace Silmaril.Proofs.SSA.Peggy.Optimizer.Extension

open Silmaril.SSA
open Silmaril.SSA.Peggy.Optimizer.Extension
open Silmaril.SSA.Peggy.Acyclic (Ranked)
open RVSDG (Tuple Port)

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params ins : List (PEG.Ty Data)} {out : PEG.Ty Data} {n : Nat}
variable {g : PEG.Graph P params [out] n 0}
variable (label : PEG.Label P params (Fin 0) ins out) (args : Tuple (PEG.Ref g.sort) ins)

private theorem get_map {S : Type} {F G : S → Type} {ts : List S} {t : S}
    (xs : Tuple F ts) (p : Port ts t) (f : ∀ s, F s → G s) :
    (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs; exact ih _

private theorem arg_succ (i : Fin n) (j : Fin (g.node i).inputs.length) :
    ((prepend g label args).node i.succ).arg j = liftRef out ((g.node i).arg j) :=
  get_map _ _ _

private theorem rank_bound (rank : Fin n → Nat) (i : Fin n)
    (vertices : List (Fin n)) (mem : i ∈ vertices) :
    rank i + 1 ≤ vertices.foldr (fun v cap => max (rank v + 1) cap) 0 := by
  induction vertices with
  | nil => exact (List.not_mem_nil mem).elim
  | cons head tail ih =>
    rcases List.mem_cons.mp mem with eq | inTail
    · subst head
      exact Nat.le_max_left _ _
    · exact (ih inTail).trans (Nat.le_max_right _ _)

theorem prepend_decreases (before : Ranked g) (i : Fin (n + 1))
    (j : Fin ((prepend g label args).node i).inputs.length) :
    prependRank before.rank (((prepend g label args).node i).arg j).id <
      prependRank before.rank i := by
  refine Fin.cases ?fresh ?old i j
  · intro slot
    change Fin ins.length at slot
    change prependRank before.rank
        (((args.map fun _ => liftRef out).get (PEG.portAt ins slot)).id) <
      prependRank before.rank 0
    rw [get_map]
    exact rank_bound before.rank (args.get (PEG.portAt ins slot)).id _
      (List.mem_finRange _)
  · intro v slot
    change Fin (g.node v).inputs.length at slot
    have rank_eq := congrArg
      (fun ref : PEG.Ref (sorts g.sort out) (g.node v).inputs[slot] =>
        prependRank before.rank ref.id)
      (arg_succ label args v slot)
    exact rank_eq.trans_lt (before.decreases v slot)

theorem fold_succ (before : Ranked g) (after : Ranked (prepend g label args))
    (F : PEG.Ty Data → Type)
    (step : ∀ {ts t}, PEG.Label P params (Fin 0) ts t →
      (∀ j : Fin ts.length, F ts[j]) → F t)
    (i : Fin n) : after.fold F step i.succ = before.fold F step i := by
  induction i using (measure before.rank).wf.induction with
  | h i ih =>
    rw [Ranked.fold, Ranked.fold]
    change step (g.node i).label _ = step (g.node i).label _
    congr 1
    funext j
    change Fin (g.node i).inputs.length at j
    have edge := congrArg
      (fun ref : PEG.Ref (sorts g.sort out) (g.node i).inputs[j] =>
        Eq.ndrec (motive := F) (after.fold F step ref.id) ref.typed)
      (arg_succ label args i j)
    exact edge.trans (congrArg (fun value => ((g.node i).arg j).typed ▸ value)
      (ih _ (before.decreases i j)))

end Silmaril.Proofs.SSA.Peggy.Optimizer.Extension
