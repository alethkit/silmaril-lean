module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Proofs

open CategoryTheory
open RVSDG (Locals Origin Port Tuple)

variable {P Q R : Signature}
variable {args target next : List ValueSort} {past : List (List ValueSort)}
variable {version cells : Nat}

private theorem lift_id :
    @liftPortMap args args (fun p => p) = (fun {_} p => p) := by
  funext sort p
  cases p <;> rfl

private theorem lift_comp (rename : PortMap args target) (rename' : PortMap target next) :
    @liftPortMap args next (fun p => rename' (rename p)) =
      (fun {_} p => liftPortMap rename' (liftPortMap rename p)) := by
  funext sort p
  cases p <;> rfl

private theorem mapOrigin_id {sort : ValueSort} (wire : Origin args past sort) :
    mapOrigin (fun p => p) wire = wire := by
  cases wire <;> rfl

private theorem mapOrigin_comp (rename : PortMap args target) (rename' : PortMap target next)
    {sort : ValueSort} (wire : Origin args past sort) :
    mapOrigin (fun p => rename' (rename p)) wire = mapOrigin rename' (mapOrigin rename wire) := by
  cases wire <;> rfl

private theorem mapBody_id (body : Body args past version) :
    mapBody (fun p => p) body = body := by
  induction body <;> simp only [mapBody, mapOrigin_id, *]

private theorem mapBody_comp (rename : PortMap args target) (rename' : PortMap target next)
    (body : Body args past version) :
    mapBody (fun p => rename' (rename p)) body = mapBody rename' (mapBody rename body) := by
  induction body <;> simp only [mapBody, mapOrigin_comp, *]

theorem mapGraph_id (graph : Graph P.args) : mapGraph (𝟙 P) graph = graph := by
  change Graph.mk graph.merge (fun edge => mapBody (fun p => p) (graph.arm edge))
    (mapBody (liftPortMap (fun p => p)) graph.suffix) = graph
  simp only [lift_id, mapBody_id]

theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R) (graph : Graph P.args) :
    mapGraph (h ≫ k) graph = mapGraph k (mapGraph h graph) := by
  change Graph.mk graph.merge
    (fun edge => mapBody (fun p => Signature.Hom.port k (Signature.Hom.port h p)) (graph.arm edge))
    (mapBody (liftPortMap (fun p => Signature.Hom.port k (Signature.Hom.port h p))) graph.suffix) = _
  simp only [mapBody_comp, lift_comp, mapGraph]

theorem pullInput_get (rename : PortMap args target) (input : Tuple (Val cells) target)
    {sort : ValueSort} (p : Port args sort) :
    (pullInput rename input).get p = input.get (rename p) := by
  induction p with
  | head => rfl
  | tail p ih => exact ih (fun p => rename (.tail p))

private theorem tuple_ext :
    {args : List ValueSort} → (input other : Tuple (Val cells) args) →
      (∀ {sort} (p : Port args sort), input.get p = other.get p) → input = other
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons a input, .cons b other, equal => by
    have head : a = b := equal .head
    have tail := tuple_ext input other (fun p => equal (.tail p))
    rw [head, tail]

theorem pullInput_lift (rename : PortMap args target) (word : Word)
    (input : Tuple (Val cells) target) :
    pullInput (liftPortMap rename) (.cons word input) = .cons word (pullInput rename input) := by
  apply tuple_ext
  intro sort p
  cases p with
  | head => rfl
  | tail p =>
    exact (pullInput_get (liftPortMap rename) (.cons word input) (.tail p)).trans
      (pullInput_get rename input p).symm

private theorem pullInput_id (input : Tuple (Val cells) args) :
    pullInput (fun p => p) input = input :=
  tuple_ext _ _ (pullInput_get (fun p => p) input)

private theorem pullInput_comp (rename : PortMap args target) (rename' : PortMap target next)
    (input : Tuple (Val cells) next) :
    pullInput (fun p => rename' (rename p)) input = pullInput rename (pullInput rename' input) := by
  induction args with
  | nil => rfl
  | cons _ _ ih => simp only [pullInput, pullInput_get, ih]

theorem reduct_id (model : Model P) : reduct (𝟙 P) model = model := by
  cases model with
  | mk cells input => exact congrArg (Model.mk cells) (pullInput_id input)

theorem reduct_comp (h : P ⟶ Q) (k : Q ⟶ R) (model : Model R) :
    reduct (h ≫ k) model = reduct h (reduct k model) :=
  congrArg (Model.mk model.cells)
    (pullInput_comp (Signature.Hom.port h) (Signature.Hom.port k) model.input)

private theorem read_mapOrigin (rename : PortMap args target) {sort : ValueSort}
    (wire : Origin args past sort) (input : Tuple (Val cells) target)
    (locals : Locals (Val cells) past) :
    readValue (mapOrigin rename wire) input locals = readValue wire (pullInput rename input) locals := by
  cases wire with
  | arg p => exact (pullInput_get rename input p).symm
  | output _ _ => rfl

private theorem denote_mapBody (rename : PortMap args target) (body : Body args past version)
    (input : Tuple (Val cells) target) (locals : Locals (Val cells) past) (initial : Heap cells) :
    (mapBody rename body).denote input locals initial =
      body.denote (pullInput rename input) locals initial := by
  induction body generalizing initial with
  | ret => simp only [mapBody, Body.denote, read_mapOrigin]
  | load _ _ _ ih =>
    simp only [mapBody, Body.denote, read_mapOrigin]
    exact ih _ _
  | store _ _ _ _ ih => simp only [mapBody, Body.denote, read_mapOrigin, ih]

theorem observe_mapGraph (h : P ⟶ Q) (model : Model Q) (graph : Graph P.args)
    (guard : Bool) (initial : Heap model.cells) :
    model.observe (mapGraph h graph) guard initial = (reduct h model).observe graph guard initial := by
  simp only [Model.observe, Diamond.Graph.denote, mapGraph, Memory.Graph.denote, reduct]
  let rename : PortMap P.args Q.args := Signature.Hom.port h
  rw [denote_mapBody rename (graph.arm _) model.input PUnit.unit initial]
  let selected := (graph.arm (Diamond.Projection.ofBool guard)).denote
    (pullInput rename model.input) initial
  exact (denote_mapBody (liftPortMap rename) graph.suffix
    (.cons selected.1 model.input) PUnit.unit selected.2).trans
    (congrArg (fun input => graph.suffix.denote input selected.2)
      (pullInput_lift rename selected.1 model.input))

theorem holds_iff_returns (e : Equation P) (model : Model P) :
    e.Holds model ↔ ∀ guard (initial : Heap model.cells) value final,
      e.lhs.Returns guard model.input initial value final ↔
        e.rhs.Returns guard model.input initial value final := by
  have returns (graph : Graph P.args) (guard : Bool) (initial : Heap model.cells)
      (value : Word) (final : Heap model.cells) :
      graph.Returns guard model.input initial value final ↔
        model.observe graph guard initial = (value, final) :=
    graph.returns_iff_denote guard model.input initial value final
  simp only [returns]
  constructor
  · intro equal guard initial value final
    rw [equal guard initial]
  · intro agrees guard initial
    let result := model.observe e.lhs guard initial
    exact ((agrees guard initial result.1 result.2).1 rfl).symm

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Proofs
