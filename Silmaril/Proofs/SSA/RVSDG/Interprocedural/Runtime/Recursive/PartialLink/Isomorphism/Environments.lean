module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Proofs

universe u v w

variable {T : Type u} {F : T → Type w}

private def colours {ports : Ports T} : Tuple F ports → List (Sigma F)
  | .nil => []
  | @Tuple.cons _ _ t _ value rest => ⟨t, value⟩ :: colours rest

private theorem colours_get {ports : Ports T} {t : T} (values : Tuple F ports) (p : Port ports t) :
    (colours values)[p.index]? = some ⟨t, values.get p⟩ := by
  induction p with
  | head => cases values; rfl
  | tail _ ih => cases values with | cons _ tail => exact ih tail

private def rows {past : List (Ports T)} : Locals F past → List (List (Sigma F)) :=
  match past with
  | [] => fun _ => []
  | _ :: _ => fun values => colours values.1 :: rows values.2

private theorem rows_length {past : List (Ports T)} (values : Locals F past) :
    (rows values).length = past.length := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ (ih values.2)

private theorem rows_snoc {past : List (Ports T)} {ports : Ports T} (values : Locals F past)
    (next : Tuple F ports) : rows (values.snoc next) = rows values ++ [colours next] := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact congrArg (colours values.1 :: ·) (ih values.2)

private theorem rows_get {past : List (Ports T)} (values : Locals F past) (i : Fin past.length) :
    (rows values)[i.val]? = some (colours (values.get i)) := by
  induction past with
  | nil => exact i.elim0
  | cons _ _ ih => exact Fin.cases rfl (fun j => ih values.2 j) i

private def lookup (all : List (List (Sigma F))) (i p : Nat) : Option (Sigma F) :=
  all[i]?.bind fun values => values[p]?

private theorem lookup_snoc (all : List (List (Sigma F))) (next : List (Sigma F)) (i p : Nat) :
    lookup (all ++ [next]) i p = if i = all.length then next[p]? else lookup all i p := by
  by_cases equal : i = all.length
  · subst i
    simp only [lookup, ite_true, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.bind_some]
  by_cases before : i < all.length
  · simp only [lookup, ite_eq_right equal, List.getElem?_append_left before]
  have later : all.length < i := by omega
  have missing : all[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
  have noNext : [next][i - all.length]? = none :=
    List.getElem?_eq_none_iff.mpr (by simp only [List.length_singleton]; omega)
  simp only [lookup, ite_eq_right equal, List.getElem?_append_right (Nat.le_of_lt later), noNext, missing]

private theorem lookup_snoc_empty (all : List (List (Sigma F))) (i p : Nat) :
    lookup (all ++ [[]]) i p = lookup all i p := by
  rw [lookup_snoc]
  split
  · rename_i equal
    have missing : all[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    simp [lookup, missing]
  · rfl

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args ports portsL portsR : Ports (Ty V S)} {pastL pastR : List (Ports (Ty V S))}
variable {rename : Nat → Nat}

private inductive ColourPair (m : Machine.{u, v, w} Op) (ids : GlobalRel) : Sigma m.Val → Sigma m.Val → Prop where
  | related {t : Ty V S} {left right : m.Val t} (pair : ValueRelated m ids left right) :
    ColourPair m ids ⟨t, left⟩ ⟨t, right⟩

private theorem colour_at {left : Tuple m.Val portsL} {right : Tuple m.Val portsR}
    (pair : TupleRelated m ids left right) (p : Nat) {a b : Sigma m.Val}
    (atL : (colours left)[p]? = some a) (atR : (colours right)[p]? = some b) :
    ColourPair m ids a b := by
  induction p generalizing portsL portsR a b with
  | zero =>
    cases pair with
    | nil => cases atL
    | cons head _ =>
      have aEq := Option.some.inj atL
      have bEq := Option.some.inj atR
      subst a
      subst b
      exact .related head
  | succ p ih =>
    cases pair with
    | nil => cases atL
    | cons _ tail => exact ih tail atL atR

/-- Compare the existing typed outputs at each pair of corresponding producer
addresses. At an empty φ there is no output port to observe. -/
def LocalsRelated (m : Machine.{u, v, w} Op) (ids : GlobalRel) (rename : Nat → Nat)
    (left : Locals m.Val pastL) (right : Locals m.Val pastR) : Prop :=
  ∀ i p {a b : Sigma m.Val}, lookup (rows left) i p = some a →
    lookup (rows right) (rename i) p = some b → ColourPair m ids a b

namespace LocalsRelated

theorem empty : LocalsRelated m ids rename (pastL := []) (pastR := []) PUnit.unit PUnit.unit :=
  by intro i p a b atL atR; cases atL

theorem emptyLeft {left : Locals m.Val pastL} {right : Locals m.Val pastR}
    (related : LocalsRelated m ids rename left right) :
    LocalsRelated m ids rename (left.snoc (.nil : Tuple m.Val [])) right := by
  intro i p a b atL atR
  rw [rows_snoc, colours, lookup_snoc_empty] at atL
  exact related i p atL atR

theorem emptyRight {left : Locals m.Val pastL} {right : Locals m.Val pastR}
    (related : LocalsRelated m ids rename left right) :
    LocalsRelated m ids rename left (right.snoc (.nil : Tuple m.Val [])) := by
  intro i p a b atL atR
  rw [rows_snoc, colours, lookup_snoc_empty] at atR
  exact related i p atL atR

theorem snoc {left : Locals m.Val pastL} {right : Locals m.Val pastR}
    {nextL nextR : Tuple m.Val ports} (injective : Function.Injective rename)
    (position : rename pastL.length = pastR.length) (related : LocalsRelated m ids rename left right)
    (outputs : TupleRelated m ids nextL nextR) :
    LocalsRelated m ids rename (left.snoc nextL) (right.snoc nextR) := by
  intro i p a b atL atR
  rw [rows_snoc, lookup_snoc, rows_length] at atL atR
  by_cases here : i = pastL.length
  · subst i
    rw [ite_eq_left rfl] at atL
    rw [ite_eq_left position] at atR
    exact colour_at outputs p atL atR
  · have there : rename i ≠ pastR.length := fun same => here (injective (same.trans position.symm))
    rw [ite_eq_right here] at atL
    rw [ite_eq_right there] at atR
    exact related i p atL atR

end LocalsRelated

private theorem from_colour {t : Ty V S} {a b : m.Val t}
    (pair : ColourPair m ids ⟨t, a⟩ ⟨t, b⟩) : ValueRelated m ids a b := by
  cases pair with | related values => exact values

private def readOrigin {t : Ty V S} (entry : Tuple m.Val args) (locals : Locals m.Val pastL) :
    Origin args pastL t → m.Val t
  | .arg port => entry.get port
  | .output i port => (locals.get i).get port

private theorem origin_related {t : Ty V S} {inputsL inputsR : Tuple m.Val args}
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (inputs : TupleRelated m ids inputsL inputsR) (locals : LocalsRelated m ids rename localsL localsR)
    (first : Origin args pastL t) (second : Origin args pastR t)
    (edge : first.address.rename rename = second.address) :
    ValueRelated m ids (readOrigin inputsL localsL first) (readOrigin inputsR localsR second) := by
  cases first with
  | arg p =>
    cases second with
    | arg q =>
      have same := Address.arg.inj edge
      exact from_colour (colour_at inputs p.index (colours_get inputsL p) (by rw [same]; exact colours_get inputsR q))
    | output => cases edge
  | output i p =>
    cases second with
    | arg => cases edge
    | output j q =>
      obtain ⟨vertex, port⟩ := Address.output.inj edge
      exact from_colour (locals i.val p.index
        (a := ⟨t, (localsL.get i).get p⟩) (b := ⟨t, (localsR.get j).get q⟩)
        (by simp only [lookup, rows_get, Option.bind_some, colours_get])
        (by simp only [lookup, vertex, port, rows_get, Option.bind_some, colours_get]))

theorem read_related {inputsL inputsR : Tuple m.Val args}
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (inputs : TupleRelated m ids inputsL inputsR) (locals : LocalsRelated m ids rename localsL localsR)
    (left : Wires args pastL ports) (right : Wires args pastR ports)
    (edges : left.addresses.map (Address.rename rename) = right.addresses) :
    TupleRelated m ids (left.read inputsL localsL) (right.read inputsR localsR) := by
  induction left with
  | nil => cases right; exact .nil
  | cons first left ih =>
    cases right with
    | cons second right =>
      simp only [Wires.addresses, List.map_cons, List.cons.injEq] at edges
      refine .cons ?_ (ih right edges.2)
      have head := origin_related inputs locals first second edges.1
      cases first <;> cases second <;> exact head

theorem read_same {inputsL inputsR : Tuple m.Val args} {localsL localsR : Locals m.Val pastL}
    (inputs : TupleRelated m ids inputsL inputsR) (locals : LocalsRelated m ids id localsL localsR)
    (wires : Wires args pastL ports) : TupleRelated m ids (wires.read inputsL localsL) (wires.read inputsR localsR) := by
  apply read_related inputs locals
  induction wires with
  | nil => rfl
  | cons wire tail ih => cases wire <;> simp only [Wires.addresses, List.map_cons, Origin.address,
      Address.rename, id_eq, ih]

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Proofs
