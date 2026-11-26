module

public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms
public import Silmaril.SSA.Isotope.Bridge.CaseSSA.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Proofs

open CategoryTheory
open Diamond.Institution (mapDataflow mapGraph reduct)
open RVSDG (Tuple Wires)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region Tm)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

universe u v w x
variable {Data : Type u} {P Q : Diamond.Institution.Signature.{u, v} Data} {σ : Type x}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

private theorem wireTerm_map {ports : List (Ty Data)} {context : List (Code Data)}
    (h : P ⟶ Q) (layout : Layout args past context) (wires : Wires args past ports) :
    (wireTerm (Op := P.op) layout wires).mapInstr (mapPrimitive h) = wireTerm (Op := Q.op) layout wires := by
  induction wires with
  | nil => rfl
  | cons wire rest ih => simp only [wireTerm, Tm.mapInstr, ih]

private theorem schedule_map {context : List (Code Data)} (h : P ⟶ Q)
    (flow : Dataflow P.op args past sigs) (layout : Layout args past context)
    (tail : Region (Primitive P.op)) :
    (schedule flow layout tail).mapInstr (mapPrimitive h) =
      schedule (mapDataflow h flow) layout (tail.mapInstr (mapPrimitive h)) := by
  induction flow generalizing context with
  | nil => rfl
  | cons op wires rest ih =>
    simp only [schedule, Region.mapInstr, Tm.mapInstr, mapPrimitive, wireTerm_map, mapDataflow, ih]

private theorem scheduleLayout_map {context : List (Code Data)} (h : P ⟶ Q)
    (flow : Dataflow P.op args past sigs) (layout : Layout args past context) :
    scheduleLayout (mapDataflow h flow) layout = scheduleLayout flow layout := by
  induction flow generalizing context with
  | nil => rfl
  | cons op wires rest ih =>
    simp only [mapDataflow, scheduleLayout]
    exact ih (layout.push _)

private theorem finalLayout_map (h : P ⟶ Q) (g : Graph P.op inputs sigs out) :
    finalLayout (mapGraph h g) = finalLayout g :=
  scheduleLayout_map h g.dataflow _

private theorem dispatch_map (h : P ⟶ Q) (g : Graph P.op inputs sigs out) :
    (terminatorRegion (dispatch g)).mapInstr (mapPrimitive h) =
      terminatorRegion (dispatch (mapGraph h g)) := by
  simp only [dispatch, branch, slotArguments, terminatorRegion, PhiView.packTerm,
    Tm.mapInstr, Region.mapInstr, finalLayout_map]
  rfl

theorem lower_map (h : P ⟶ Q) (g : Graph P.op inputs sigs out) :
    (lower g).mapInstr (mapPrimitive h) = lower (mapGraph h g) := by
  unfold lower
  rw [Region.mapInstr, schedule_map, dispatch_map]
  rfl

private theorem encode_reduct (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    {sort : ValueSort Data} (value : sortValue m.value sort) :
    encode (reduct h m) value = encode m value := by
  cases sort <;> rfl

private theorem encodePort_reduct (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    {port : Ty Data} (value : Val m.value port) :
    encodePort (reduct h m) value = encodePort m value := by
  cases port with
  | value sort => exact encode_reduct h m value
  | state empty => exact nomatch empty
  | control => rfl

private theorem encodeTuple_reduct (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    {ports : List (Ty Data)} (values : Tuple (Val m.value) ports) :
    encodeTuple (reduct h m) values = encodeTuple m values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [encodeTuple, encodePort_reduct, ih]
    rfl

theorem instruction_reduct (h : P ⟶ Q) (m : Model.{u, v, w} Q.op) (op : Primitive P.op) :
    instruction (reduct h m) (σ := σ) op = instruction m (mapPrimitive h op) := by
  cases op with
  | apply op =>
    funext input before output after
    simp only [instruction, mapPrimitive]
    apply propext
    constructor
    · rintro ⟨values, rfl, rfl, rfl⟩
      exact ⟨values, encodeTuple_reduct h m values,
        encode_reduct h m ((reduct h m).run op values), rfl⟩
    · rintro ⟨values, rfl, rfl, rfl⟩
      exact ⟨values, (encodeTuple_reduct h m values).symm,
        (encode_reduct h m ((reduct h m).run op values)).symm, rfl⟩

theorem eval_lower_map (h : P ⟶ Q) (g : Graph P.op inputs sigs out) (m : Model.{u, v, w} Q.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) (start finish : σ) (label : Nat)
    (payload : Value (Atom m)) :
    Eval (instruction m) (inputEnv m input) ((lower g).mapInstr (mapPrimitive h)) start label payload finish ↔
      Eval (instruction (reduct h m)) (inputEnv (reduct h m) input) (lower g) start label payload finish := by
  rw [lower_map]
  refine (lower_eval_iff (mapGraph h g) m input start finish label payload).trans ?_
  refine Iff.trans ?_ (lower_eval_iff g (reduct h m) input start finish label payload).symm
  have outputs := (congrArg (encode m) (Diamond.Institution.denote_mapGraph h m g input)).trans
    (encode_reduct h m (g.denote (reduct h m) input)).symm
  exact Iff.of_eq (congrArg (fun value => label = 0 ∧ payload = value ∧ finish = start) outputs)

theorem satisfaction (e : Diamond.Institution.Equation P) (m : Model.{u, v, w} P.op) :
    (lowerEquation e).Holds m ↔ e.Holds m := by
  constructor
  · intro holds input
    have runLeft := (lower_eval_iff e.lhs m input () () 0 (encode m (e.lhs.denote m input))).2
      ⟨rfl, rfl, rfl⟩
    have runRight := (holds input 0 (encode m (e.lhs.denote m input))).1 runLeft
    exact encode_injective m
      ((lower_eval_iff e.rhs m input () () 0 (encode m (e.lhs.denote m input))).1 runRight).2.1
  · intro holds input label payload
    change Eval (instruction m) (inputEnv m input) (lower e.lhs) () label payload () ↔
      Eval (instruction m) (inputEnv m input) (lower e.rhs) () label payload ()
    refine (lower_eval_iff e.lhs m input () () label payload).trans ?_
    refine Iff.trans ?_ (lower_eval_iff e.rhs m input () () label payload).symm
    exact Iff.of_eq (congrArg (fun result => label = 0 ∧ payload = encode m result ∧ () = ())
      (holds input))

end Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Proofs
