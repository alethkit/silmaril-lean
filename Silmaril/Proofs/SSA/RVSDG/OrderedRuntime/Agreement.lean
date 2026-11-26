module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Defs
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Proofs

open CategoryTheory CategoryTheory.Category
open Silmaril.RuntimeWires
open Silmaril.RuntimeWires.Presentation (Computations)

universe u v w
variable {G : EffectfulPolygraph.{u, v}}
variable {F : Ty G → Type w}
variable {root A B : List G.Obj} {past sigs : List (Ports (Ty G))}

private def newest {head : Ports (Ty G)} :
    (past : List (Ports (Ty G))) → Locals F (past ++ [head]) → Tuple F head
  | [], locals => locals.1
  | _ :: tail, locals => newest tail locals.2

private theorem newest_snoc {head : Ports (Ty G)} (past : List (Ports (Ty G)))
    (locals : Locals F past) (tuple : Tuple F head) :
    newest past (locals.snoc tuple) = tuple := by
  induction past with
  | nil => rfl
  | cons _ tail ih => exact ih locals.2

private theorem get_newest {head : Ports (Ty G)} (past : List (Ports (Ty G))) {t : Ty G}
    (p : Port head t) (locals : Locals F (past ++ [head])) :
    (locals.get (lastIndex head past)).get (lastPort p past) = (newest past locals).get p := by
  induction past with
  | nil => rfl
  | cons _ tail ih => exact ih locals.2

private theorem read_route {args ts : Ports (Ty G)}
    (resolve : ∀ t, Origin args past t → F t)
    (tuple : Tuple F ts) (f : ∀ {t : Ty G}, Port ts t → Origin args past t)
    (agrees : ∀ {t : Ty G} (p : Port ts t), resolve t (f p) = tuple.get p) :
    (route ts f).map resolve = tuple := by
  induction tuple with
  | nil => rfl
  | cons x tail ih =>
    simp only [route, Tuple.map]
    exact congrArg₂ Tuple.cons (agrees .head) (ih (fun p => f (.tail p)) (fun p => agrees (.tail p)))

private def current (f : Frontier G root past A) (entry : Tuple F (ports G root))
    (locals : Locals F past) : Tuple F (ports G A) :=
  match f with
  | .entry => entry
  | .vertex past _ => newest past locals

private theorem frontier_read (f : Frontier G root past A) (entry : Tuple F (ports G root))
    (locals : Locals F past) : (route _ f.origin).read entry locals = current f entry locals := by
  apply read_route
  intro t p
  cases f with
  | entry => rfl
  | vertex past A => exact get_newest past p locals

variable (m : Model.{u, v, w} G)

set_option backward.isDefEq.respectTransparency false in
private theorem eval_fold {f : Frontier G root past A}
    {t : Term (Opcode G) (ports G root) past sigs (ports G B)} (h : Chain G root B f t)
    (entry : Tuple m.Val (ports G root)) (locals : Locals m.Val past) :
    t.eval m.toRVSDG entry locals =
      (h.fold (C := Type (max u w)) (fun word => Tuple m.Val (ports G word))
        (fun op => ↾m.step op)) (current f entry locals) := by
  induction h with
  | ret f => exact frontier_read f entry locals
  | @bind A next past sigs f op rest checked ih =>
    rw [Chain.fold, Term.eval]
    have hf := frontier_read f entry locals
    change rest.eval m.toRVSDG entry (locals.snoc (m.step op ((route _ f.origin).read entry locals))) = _
    rw [hf, ih]
    have hn : current (.vertex past next) entry (locals.snoc (m.step op (current f entry locals))) =
        m.step op (current f entry locals) :=
      newest_snoc past locals _
    rw [hn]
    rfl

theorem denoteFunctions_run (g : Graph (Opcode G) (ports G A) [] sigs (ports G B))
    (h : Chain G A B .entry g.toTerm) (input : Tuple m.Val (ports G A)) :
    denoteFunctions m g h input = g.run m.toRVSDG input :=
  (eval_fold m h input PUnit.unit).symm.trans (Graph.run_toTerm g m.toRVSDG input)

set_option backward.isDefEq.respectTransparency false in
private theorem realization_fold (I : Computations G ⥤ Type (max u w)) (e : Realization m I)
    {f : Frontier G root past A} {t : Term (Opcode G) (ports G root) past sigs (ports G B)}
    (h : Chain G root B f t) (input : Tuple m.Val (ports G A)) :
    I.map (h.fold (fun word => (⟨word⟩ : Computations G)) Instruction.arrow) (e.encode A input) =
      e.encode B ((h.fold (fun word => Tuple m.Val (ports G word)) (fun op => ↾m.step op)) input) := by
  induction h with
  | ret f =>
    rw [Chain.fold, Functor.map_id]
    rfl
  | bind f op rest ih =>
    simp only [Chain.fold, Functor.map_comp, types_comp_apply]
    rw [e.step, ih]
    rfl

theorem denote_run (I : Computations G ⥤ Type (max u w)) (e : Realization m I)
    (g : Graph (Opcode G) (ports G A) [] sigs (ports G B))
    (h : Chain G A B .entry g.toTerm) (input : Tuple m.Val (ports G A)) :
    I.map (denote g h) (e.encode A input) = e.encode B (g.run m.toRVSDG input) :=
  (realization_fold m I e h input).trans (congrArg (e.encode B) (denoteFunctions_run m g h input))

end Silmaril.SSA.RVSDG.OrderedRuntime.Proofs
