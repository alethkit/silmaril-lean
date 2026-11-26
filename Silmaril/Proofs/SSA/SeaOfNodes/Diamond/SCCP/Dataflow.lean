module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Dataflow.Defs
public import Silmaril.Semantics.Dataflow.Flat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Proofs

open Semantics.Dataflow (Flat)
open RVSDG (Port Tuple Locals Wires)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {args ports : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {m : Model.{u, v, w} Op}

private def TupleRel {F G : Ty Data → Type w} (rel : ∀ t, F t → G t → Prop)
    (lhs : Tuple F ports) (rhs : Tuple G ports) : Prop :=
  ∀ {t} (p : Port ports t), rel t (lhs.get p) (rhs.get p)

private def LocalsRel {F G : Ty Data → Type w} (rel : ∀ t, F t → G t → Prop)
    (lhs : Locals F past) (rhs : Locals G past) : Prop :=
  ∀ vertex, TupleRel rel (lhs.get vertex) (rhs.get vertex)

private theorem wires_rel {F G : Ty Data → Type w} {rel : ∀ t, F t → G t → Prop}
    (wires : Wires args past ports) {lhsArgs : Tuple F args} {rhsArgs : Tuple G args}
    {lhs : Locals F past} {rhs : Locals G past}
    (hargs : TupleRel rel lhsArgs rhsArgs) (hlocals : LocalsRel rel lhs rhs) :
    TupleRel rel (wires.read lhsArgs lhs) (wires.read rhsArgs rhs) := by
  intro t port
  induction wires generalizing t with
  | nil => cases port
  | cons wire _ ih =>
    cases port with
    | head =>
      cases wire with
      | arg p => exact hargs p
      | output i p => exact hlocals i p
    | tail p => exact ih p

private theorem snoc_rel {F G : Ty Data → Type w} {rel : ∀ t, F t → G t → Prop}
    {lhs : Locals F past} {rhs : Locals G past} {x : Tuple F ports} {y : Tuple G ports}
    (h : LocalsRel rel lhs rhs) (hnew : TupleRel rel x y) :
    LocalsRel rel (lhs.snoc x) (rhs.snoc y) := by
  induction past with
  | nil =>
    exact fun i => Fin.cases (motive := fun j =>
      TupleRel rel ((lhs.snoc x).get j) ((rhs.snoc y).get j)) hnew (fun j => j.elim0) i
  | cons head tail ih =>
    exact fun i => Fin.cases (motive := fun j =>
      TupleRel rel ((lhs.snoc x).get j) ((rhs.snoc y).get j)) (h 0)
      (fun j => ih (fun k => h k.succ) j) i

private theorem gather_covers {facts : Tuple (Fact m.value) ports} {xs : Tuple (Val m.value) ports}
    (h : TupleCovers facts xs) : (gather facts).Covers xs := by
  induction facts with
  | nil => cases xs; rfl
  | cons _ _ ih =>
    cases xs with
    | cons _ _ => exact Flat.map₂_covers Tuple.cons (h .head) (ih fun p => h (.tail p))

theorem evalFacts_cover (flow : Dataflow Op args past sigs)
    {entryFacts : Tuple (Fact m.value) args} {entry : Tuple (Val m.value) args}
    (hentry : TupleCovers entryFacts entry)
    {facts : Locals (Fact m.value) past} {locals : Locals (Val m.value) past}
    (hlocals : LocalsCover facts locals) :
    LocalsCover (evalFacts m entryFacts flow facts) (flow.eval m entry locals) := by
  induction flow with
  | nil => exact hlocals
  | cons op wires _ ih =>
    apply ih
    apply snoc_rel (rel := fun t => @Flat.Covers (Val m.value t)) hlocals
    intro t port
    cases port with
    | head =>
      exact Flat.map_covers (m.run op)
        (gather_covers (wires_rel (rel := fun t => @Flat.Covers (Val m.value t)) wires hentry hlocals))
    | tail p => cases p

private theorem gather_mono {lhs rhs : Tuple (Fact m.value) ports}
    (le : TupleLE lhs rhs) : gather lhs ≤ gather rhs := by
  induction lhs with
  | nil => cases rhs; exact le_rfl
  | cons _ _ ih =>
    cases rhs with
    | cons _ _ => exact Flat.map₂_mono Tuple.cons (le .head) (ih fun p => le (.tail p))

theorem evalFacts_mono (flow : Dataflow Op args past sigs)
    {lhsArgs rhsArgs : Tuple (Fact m.value) args} (hargs : TupleLE lhsArgs rhsArgs)
    {lhs rhs : Locals (Fact m.value) past} (hlocals : LocalsLE lhs rhs) :
    LocalsLE (evalFacts m lhsArgs flow lhs) (evalFacts m rhsArgs flow rhs) := by
  induction flow with
  | nil => exact hlocals
  | cons op wires _ ih =>
    apply ih
    apply snoc_rel (rel := fun _ x y => x ≤ y) hlocals
    intro t port
    cases port with
    | head =>
      exact Flat.map_mono (m.run op) (gather_mono (wires_rel (rel := fun _ x y => x ≤ y) wires hargs hlocals))
    | tail p => cases p

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Proofs
