module

public import Silmaril.SSA.Peggy.EPEG.Defs
import Silmaril.SSA.PEG.Semantics.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG

open Silmaril.SSA
open Silmaril.SSA.Peggy.EPEG
open RVSDG (Tuple Port)

universe u v x

variable {Data : Type u} {P : PEG.InstructionSet.{u,v} Data}
variable {params results : List (PEG.Ty Data)} {n n' l : Nat}
variable {g : PEG.Graph P params results n l} {m : PEG.Interpretation.{u,v,x} P}
variable {values : g.Valuation m} {env : Tuple m.Value params}

theorem read_heq {t : PEG.Ty Data} (ref : PEG.Ref g.sort t)
    (value : Option (m.Value (g.sort ref.id))) : HEq (ref.read m.carrier value) value := by
  obtain ⟨id, h⟩ := ref
  cases h
  rfl

theorem read_eq {t : PEG.Ty Data} {a b : PEG.Ref g.sort t} (i : PEG.Index l)
    (agree : StreamEq values a.id b.id) :
    a.read m.carrier (values (a.id, i)) = b.read m.carrier (values (b.id, i)) :=
  eq_of_heq ((read_heq a _).trans ((agree.2 i).trans (read_heq b _).symm))

theorem merge_sound {classes : Classes n} {a b : Fin n}
    (valid : classes.Valid values) (evidence : StreamEq values a b) :
    (classes.merge a b).Valid values := by
  let rep v := if classes v = classes b then a else v
  have move (v : Fin n) : StreamEq values v (rep v) := by
    dsimp only [rep]
    split
    next h => exact ⟨(valid _ _ h).1.trans evidence.1.symm,
      fun i => ((valid _ _ h).2 i).trans (evidence.2 i).symm⟩
    next => exact ⟨rfl, fun _ => HEq.rfl⟩
  intro p q same
  have center := valid (rep p) (rep q) same
  exact ⟨(move p).1.trans (center.1.trans (move q).1.symm),
    fun i => ((move p).2 i).trans ((center.2 i).trans ((move q).2 i).symm)⟩

theorem merge_guarded_sound {classes : Classes n} (rule : GuardedEquation g)
    (valid : classes.Valid values) (law : rule.Holds values) (check : rule.check classes = true) :
    (classes.merge rule.conclusion.lhs rule.conclusion.rhs).Valid values := by
  apply merge_sound valid
  apply law
  intro guard member
  exact valid _ _ (beq_iff_eq.mp (List.all_eq_true.mp check guard member))

@[expose] noncomputable def nodeValue {t : PEG.Ty Data} (node : PEG.Node P params (Fin l) g.sort t)
    (values : g.Valuation m) (env : Tuple m.Value params) (i : PEG.Index l) : Option (m.Value t) :=
  node.label.interpret m env i fun slot j _ =>
    let ref := node.arg slot
    ref.read m.carrier (values (ref.id, j))

theorem nodeValue_heq {s t : PEG.Ty Data} (sortEq : s = t)
    {a : PEG.Node P params (Fin l) g.sort s} {b : PEG.Node P params (Fin l) g.sort t}
    (nodeEq : HEq a b) (i : PEG.Index l) :
    HEq (nodeValue a values env i) (nodeValue b values env i) := by
  cases sortEq
  cases eq_of_heq nodeEq
  rfl

theorem congruent_streams {a b : Fin n} (pair : MatchingNodes g a b)
    (solves : g.Solves m env values)
    (operands : ∀ k : Fin pair.inputs.length, StreamEq values
      (pair.lhsArgs.get (PEG.portAt pair.inputs k)).id
      (pair.rhsArgs.get (PEG.portAt pair.inputs k)).id) :
    StreamEq values a b := by
  refine ⟨pair.lhsSort.trans pair.rhsSort.symm, fun i => ?_⟩
  have left := (heq_of_eq (solves (a, i))).trans (nodeValue_heq pair.lhsSort pair.lhsNode i)
  have right := (heq_of_eq (solves (b, i))).trans (nodeValue_heq pair.rhsSort pair.rhsNode i)
  have same : nodeValue (PEG.Node.ofLabel pair.label pair.lhsArgs) values env i =
      nodeValue (PEG.Node.ofLabel pair.label pair.rhsArgs) values env i := by
    unfold nodeValue
    apply congrArg (pair.label.interpret m env i)
    funext slot j legal
    exact read_eq j (operands slot)
  exact left.trans ((heq_of_eq same).trans right.symm)

theorem merge_congruent_sound {classes : Classes n} {a b : Fin n} (pair : MatchingNodes g a b)
    (solves : g.Solves m env values) (valid : classes.Valid values)
    (check : pair.checkOperands classes = true) : (classes.merge a b).Valid values :=
  merge_sound valid (congruent_streams pair solves fun k =>
    valid _ _ (beq_iff_eq.mp (List.all_eq_true.mp check k (List.mem_finRange k))))

variable {target : PEG.Graph P params results n' l}

theorem selection_demandWellFounded {candidate : Selection g target} {classes : Classes n}
    (check : candidate.check classes = true) : WellFounded target.Demand :=
  target.demandWellFounded_of_check candidate.rank (Bool.and_eq_true_iff.mp check).1

private theorem get_map {S : Type u} {F : S → Type v} {G : S → Type x} {ts : List S} {t : S}
    (f : ∀ s, F s → G s) (xs : Tuple F ts) (p : Port ts t) :
    (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs; exact ih _

private theorem tuple_eq {F : PEG.Ty Data → Type x} {ts : List (PEG.Ty Data)} (xs ys : Tuple F ts)
    (h : ∀ i : Fin ts.length, xs.get (PEG.portAt ts i) = ys.get (PEG.portAt ts i)) :
    xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys => exact congrArg₂ Tuple.cons (h 0) (ih ys (fun i => h i.succ))

theorem read_sourceRef (candidate : Selection g target) {t : PEG.Ty Data}
    (ref : PEG.Ref target.sort t) (i : PEG.Index l) :
    ref.read m.carrier (candidate.inherit values (ref.id, i)) =
      (candidate.sourceRef ref).read m.carrier (values ((candidate.sourceRef ref).id, i)) := by
  obtain ⟨id, h⟩ := ref
  cases h
  rfl

theorem selection_sound (candidate : Selection g target) {classes : Classes n}
    (sourceWF : WellFounded g.Demand) (targetWF : WellFounded target.Demand)
    (valid : classes.Valid (g.denote m env sourceWF)) (check : candidate.check classes = true)
    (solves : target.Solves m env (candidate.inherit (g.denote m env sourceWF))) (i : PEG.Index l) :
    g.observe m (g.denote m env sourceWF) i = target.observe m (target.denote m env targetWF) i := by
  rw [target.solves_unique m env targetWF (target.denote_solves m env targetWF) solves]
  apply tuple_eq
  intro j
  have root := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp check).2) j (List.mem_finRange j)
  simp only [PEG.Graph.observe, get_map, read_sourceRef]
  exact read_eq i (valid _ _ (beq_iff_eq.mp root))

end Silmaril.Proofs.SSA.Peggy.EPEG
