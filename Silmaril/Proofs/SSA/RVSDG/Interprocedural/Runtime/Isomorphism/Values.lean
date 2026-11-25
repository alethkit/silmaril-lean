module

public import Mathlib.Data.List.Forall2
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Defs
public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Isomorphism.Trace

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs

open RVSDG.Isomorphism.Proofs (colours colours_get)
open NestedTheta.Isomorphism.Proofs (Slots store read lookup read_colours Erased)

universe u v w a b c d

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args args' ports ports' : Ports (Ty V S)}
variable {past past' : List (Ports (Ty V S))}

theorem prepend_related {params contextL contextR : Ports (Ty V S)} {inputsL inputsR : Tuple m.Val params}
    {captureL : Tuple m.Val contextL} {captureR : Tuple m.Val contextR}
    (inputs : TupleRelated m ids inputsL inputsR) (captured : TupleRelated m ids captureL captureR) :
    TupleRelated m ids (prependContext inputsL captureL) (prependContext inputsR captureR) := by
  induction captureL generalizing contextR with
  | nil => cases captured; exact inputs
  | cons value rest ih =>
    cases captured with
    | cons head tail => exact .cons head (ih tail)

inductive TagRelated (m : Machine.{u, v, w} Op) (ids : GlobalRel) :
    Sigma m.Val → Sigma m.Val → Prop where
  | tagged {t : Ty V S} {left right : m.Val t} (values : ValueRelated m ids left right) :
      TagRelated m ids ⟨t, left⟩ ⟨t, right⟩

abbrev TagList (m : Machine.{u, v, w} Op) (ids : GlobalRel) :=
  List.Forall₂ (TagRelated m ids)

abbrev StoreSlot (m : Machine.{u, v, w} Op) (ids : GlobalRel) :=
  Option.Rel (Option.Rel (TagList m ids))

theorem tags_of_tuple {x : Tuple m.Val ports} {y : Tuple m.Val ports'}
    (pair : TupleRelated m ids x y) : TagList m ids (colours x) (colours y) := by
  induction x generalizing ports' with
  | nil => cases pair; exact .nil
  | cons value rest ih =>
    cases pair with
    | cons head tail => exact .cons (.tagged head) (ih tail)

private theorem tuple_of_tags (x : Tuple m.Val ports) (y : Tuple m.Val ports')
    (tags : TagList m ids (colours x) (colours y)) : TupleRelated m ids x y := by
  induction x generalizing ports' with
  | nil => cases y with
    | nil => exact .nil
    | cons => cases tags
  | cons x xs ih =>
    cases y with
    | nil => cases tags
    | cons y ys =>
      obtain ⟨head, tail⟩ := List.forall₂_cons.mp tags
      cases head with
      | tagged values => exact .cons values (ih ys tail)

theorem tags_of_run {x : Option (Tuple m.Val ports)} {y : Option (Tuple m.Val ports')}
    (pair : RunRelated m ids x y) : Option.Rel (TagList m ids) (x.map colours) (y.map colours) := by
  cases pair with
  | none => exact .none
  | some pair => exact .some (tags_of_tuple pair)

private theorem run_of_tags {x : Option (Tuple m.Val ports)} {y : Option (Tuple m.Val ports')}
    (tags : Option.Rel (TagList m ids) (x.map colours) (y.map colours)) : RunRelated m ids x y := by
  cases x <;> cases y
  · exact .none
  · cases tags
  · cases tags
  · cases tags with
    | some related => exact .some (tuple_of_tags _ _ related)

theorem bind_related {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    {R : A → B → Prop} {Q : C → D → Prop} {left : Option A} {right : Option B}
    {f : A → Option C} {g : B → Option D} (entries : Option.Rel R left right)
    (steps : ∀ x y, R x y → Option.Rel Q (f x) (g y)) :
    Option.Rel Q (left.bind f) (right.bind g) := by
  cases entries with
  | none => exact .none
  | some related => exact steps _ _ related

private theorem tags_at {xs ys : List (Sigma m.Val)} (pair : TagList m ids xs ys) (i : Nat) :
    Option.Rel (TagRelated m ids) xs[i]? ys[i]? := by
  induction pair generalizing i with
  | nil => exact .none
  | cons head tail ih =>
    cases i with
    | zero => exact .some head
    | succ i => exact ih i

theorem get_related {x y : Tuple m.Val ports} (pair : TupleRelated m ids x y)
    {t : Ty V S} (p : Port ports t) : ValueRelated m ids (x.get p) (y.get p) := by
  have tags := tags_at (tags_of_tuple pair) p.index
  rw [colours_get, colours_get] at tags
  cases tags with
  | some related => cases related with | tagged values => exact values

private theorem collect_related {R : Sigma m.Val → Sigma m.Val → Prop} {xs ys : List (Option (Sigma m.Val))}
    (pair : List.Forall₂ (Option.Rel R) xs ys) :
    Option.Rel (List.Forall₂ R) (xs.mapM id) (ys.mapM id) := by
  induction pair with
  | nil => exact .some .nil
  | cons head tail ih =>
    simp only [List.mapM_cons, id]
    exact bind_related head (fun x y rel => bind_related ih (fun xs ys rest => .some (.cons rel rest)))

private theorem map_related {A : Type a} (xs : List A)
    (f g : A → Option (Sigma m.Val))
    (related : ∀ x ∈ xs, Option.Rel (TagRelated m ids) (f x) (g x)) :
    List.Forall₂ (Option.Rel (TagRelated m ids)) (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons first rest ih =>
    exact .cons (related first (List.mem_cons_self ..))
      (ih (fun x h => related x (List.mem_cons_of_mem _ h)))

theorem read_related (wiresL : Wires args past ports) (wiresR : Wires args' past' ports')
    (inL : Tuple m.Val args) (inR : Tuple m.Val args') (entry : TupleRelated m ids inL inR)
    (slotsL : Slots m.Val past) (slotsR : Slots m.Val past')
    {allL allR : Erased m.Val} (prefL : store slotsL <+: allL) (prefR : store slotsR <+: allR)
    (rename : Nat → Nat) (wires : wiresL.addresses.map (Address.rename rename) = wiresR.addresses)
    (sources : ∀ i p, Address.output i p ∈ wiresL.addresses → StoreSlot m ids allL[i]? allR[rename i]?) :
    RunRelated m ids (read wiresL inL slotsL) (read wiresR inR slotsR) := by
  apply run_of_tags
  rw [read_colours wiresL inL slotsL allL prefL, read_colours wiresR inR slotsR allR prefR,
    ← wires, List.map_map]
  apply collect_related
  apply map_related
  intro addr seen
  cases addr with
  | arg p => exact tags_at (tags_of_tuple entry) p
  | output i p =>
    have paired := sources i p seen
    have joined := bind_related (f := id) (g := id) paired (fun _ _ h => h)
    exact bind_related joined (fun _ _ h => tags_at h p)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs
