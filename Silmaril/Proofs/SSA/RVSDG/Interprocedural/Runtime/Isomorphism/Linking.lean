module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Initializers

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs

open RVSDG.Isomorphism.Proofs (site_length)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args outs outs' : Ports (Ty V S)}
variable {past past' sigs sigs' : List (Ports (Ty V S))}

private def linkRow (m : Machine.{u, v, w} Op) (unitId : Nat) :
    {outs : Ports (Ty V S)} → Vertex Op args past outs → Row m args past outs
  | _, .lambda lambda => ⟨lambda.context, lambda.captures,
      fun captured => some (.cons (.closure captured lambda.body) .nil)⟩
  | _, .delta delta => ⟨delta.context, delta.captures, fun captured =>
      let value := evalInitializer m (past := []) delta.initializer.toTerm captured PUnit.unit
      some (.cons (.global unitId past.length (value.get .head)) .nil)⟩
  | _, .phi _ => ⟨[], .nil, fun _ => none⟩

private theorem linkVertex_row (unitId : Nat) (entry : Tuple m.Val args) (values : Locals m.Val past)
    (vertex : Vertex Op args past outs) :
    linkVertex m unitId entry values vertex =
      (linkRow m unitId vertex).run ((linkRow m unitId vertex).wires.read entry values) := by
  cases vertex <;> rfl

private theorem linkTable_rows (unitId : Nat) (entry : Tuple m.Val args) (values : Locals m.Val past)
    (vertices : VertexTable Op args past sigs) (results : Wires args (extend past sigs) outs) :
    linkTable m unitId entry past sigs values vertices results =
      runRows entry past sigs values (fun i => linkRow m unitId (vertices i)) results := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    let vertex : Vertex Op args past head := vertices 0
    let row := linkRow m unitId vertex
    change (linkVertex m unitId entry values vertex).bind (fun output =>
      linkTable m unitId entry (past ++ [head]) tail (values.snoc output) (fun i => vertices i.succ) results) =
      (row.run (row.wires.read entry values)).bind (fun output =>
        runRows entry (past ++ [head]) tail (values.snoc output)
          (fun i => linkRow m unitId (vertices i.succ)) results)
    rw [linkVertex_row unitId entry values vertex]
    exact congrArg (Option.bind (row.run (row.wires.read entry values)))
      (funext fun output => ih (values.snoc output) (fun i => vertices i.succ) results)

private theorem row_wires {rename : Nat → Nat}
    (unitL unitR : Nat) {left : Vertex Op args past outs} {right : Vertex Op args past' outs'}
    (paired : Vertex.Renumbered Op rename left right) :
    (linkRow m unitL left).wires.addresses.map (Address.rename rename) =
      (linkRow m unitR right).wires.addresses := by
  cases paired with
  | lambda iso => exact iso.1.2
  | delta iso => exact iso.1.2
  | phi iso => rfl

private theorem closures_related {args : Ports (Ty V S)} {fn : Function V S} {rename : Nat → Nat}
    (left : Lambda Op args past fn) (right : Lambda Op args past' fn)
    (iso : left.Renumbered rename right)
    (capturesL : Tuple m.Val left.context) (capturesR : Tuple m.Val right.context)
    (captured : TupleRelated m ids capturesL capturesR) :
    ValueRelated m ids (.closure capturesL left.body) (.closure capturesR right.body) := by
  obtain ⟨contextL, wiresL, sigsL, bodyL⟩ := left
  obtain ⟨contextR, wiresR, sigsR, bodyR⟩ := right
  obtain ⟨⟨same, _⟩, bodies⟩ := iso
  change contextL = contextR at same
  subst contextR
  exact .closure captured bodies

private theorem linkRow_related (respects : PrimitivesRespect m ids) {rename : Nat → Nat}
    (unitL unitR : Nat) {left : Vertex Op args past outs} {right : Vertex Op args past' outs'}
    (paired : Vertex.Renumbered Op rename left right)
    (allocated : Allocates left → ids (unitL, past.length) (unitR, past'.length))
    (inputsL : Tuple m.Val (linkRow m unitL left).ins) (inputsR : Tuple m.Val (linkRow m unitR right).ins)
    (inputs : TupleRelated m ids inputsL inputsR) :
    RunRelated m ids ((linkRow m unitL left).run inputsL) ((linkRow m unitR right).run inputsR) := by
  cases paired with
  | @lambda fn left right iso =>
    exact .some (.cons (closures_related left right iso inputsL inputsR inputs) .nil)
  | @delta value left right iso =>
    have payload := initializer_related respects iso.2 inputsL inputsR inputs
    exact .some (.cons (.global (allocated trivial) (get_related payload .head)) .nil)
  | phi iso => exact .none

theorem link_related (respects : PrimitivesRespect m ids) (unitL unitR : Nat)
    {left : Omega Op args outs sigs} {right : Omega Op args outs sigs'}
    {rename : Fin sigs.length ≃ Fin sigs'.length} (iso : left.RenumberedBy right rename)
    (allocated : ∀ i, Allocates (left.region.vertices i) → ids (unitL, i.val) (unitR, (rename i).val))
    (inL inR : Tuple m.Val args) (inputs : TupleRelated m ids inL inR) :
    RunRelated m ids (linkGraph m unitL left inL) (linkGraph m unitR right inR) := by
  let empty : Locals m.Val [] := PUnit.unit
  change RunRelated m ids (linkTable m unitL inL [] sigs empty left.region.vertices left.region.results)
    (linkTable m unitR inR [] sigs' empty right.region.vertices right.region.results)
  rw [linkTable_rows unitL inL empty, linkTable_rows unitR inR empty]
  refine runRows_related rename inL inR inputs _ _ _ _
    (fun i => row_wires (m := m) unitL unitR (iso.vertices i)) iso.exports ?_
  intro i x y ready
  apply linkRow_related respects unitL unitR (iso.vertices i) _ x y ready
  intro present
  simpa only [site_length, List.length_nil, Nat.zero_add] using allocated i present

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs
