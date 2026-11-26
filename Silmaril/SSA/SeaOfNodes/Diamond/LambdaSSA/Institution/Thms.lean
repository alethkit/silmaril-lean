module

public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms
public import Silmaril.SSA.Isotope.Bridge.CaseSSA.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Coherence

/-! The typed primitive lift, CFG reindexing and satisfaction for the
generated λSSA room. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution

open CategoryTheory Silmaril.Logic.Institution
open Diamond.Institution (mapGraph reduct)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

universe u v w x
variable {Data : Type u} {P Q R : Diamond.Institution.Signature.{u, v} Data} {σ : Type x}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}

theorem mapPrimitive_preservesTypes (h : P ⟶ Q) :
    Isotope.LambdaSSA.InstructionMap.PreservesTypes (τ := Code Data) (mapPrimitive h) :=
  ⟨fun op => by cases op; rfl, fun op => by cases op; rfl⟩

theorem mapPrimitive_id (P : Diamond.Institution.Signature.{u, v} Data) :
    mapPrimitive (𝟙 P) = id :=
  funext fun | .apply _ => rfl

theorem mapPrimitive_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    mapPrimitive (h ≫ k) = mapPrimitive k ∘ mapPrimitive h :=
  funext fun | .apply _ => rfl

/-- The alphabet of the generated λSSA regions varies functorially. Each
map preserves the actual instruction source and target types. -/
def primitiveFunctor (Data : Type u) : Diamond.Institution.Signature.{u, v} Data ⥤ Type (max u v) where
  obj P := Primitive P.op
  map h := TypeCat.ofHom (mapPrimitive h)
  map_id P := congrArg TypeCat.ofHom (mapPrimitive_id P)
  map_comp h k := congrArg TypeCat.ofHom (mapPrimitive_comp h k)

/-- Instruction interpretation commutes with native model reduct. -/
theorem instruction_reduct (h : P ⟶ Q) (m : Model.{u, v, w} Q.op) (op : Primitive P.op) :
    instruction (reduct h m) (σ := σ) op = instruction m (mapPrimitive h op) :=
  Proofs.instruction_reduct h m op

/-- Relabelling the emitted CFG changes only its primitives, preserving
both occurrences of the branch into the same join. -/
theorem lower_map (h : P ⟶ Q) (g : Graph P.op inputs sigs out) :
    (lower g).mapInstr (mapPrimitive h) = lower (mapGraph h g) :=
  Proofs.lower_map h g

/-- Finite observations of the emitted CFG commute with reindexing, for
any ambient state type. -/
theorem eval_lower_map (h : P ⟶ Q) (g : Graph P.op inputs sigs out) (m : Model.{u, v, w} Q.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) (start finish : σ) (label : Nat)
    (payload : Value (Atom m)) :
    Eval (instruction m) (inputEnv m input) ((lower g).mapInstr (mapPrimitive h)) start label payload finish ↔
      Eval (instruction (reduct h m)) (inputEnv (reduct h m) input) (lower g) start label payload finish :=
  Proofs.eval_lower_map h g m input start finish label payload

theorem GeneratedRegion.hasType (r : GeneratedRegion P inputs out) :
    r.val.HasType (initialContext inputs) [sortCode out] := by
  obtain ⟨_, g, eq⟩ := r.property
  exact eq ▸ lower_hasType g

def GeneratedRegion.map (r : GeneratedRegion P inputs out) (h : P ⟶ Q) :
    GeneratedRegion Q inputs out :=
  ⟨r.val.mapInstr (mapPrimitive h), by
    obtain ⟨sigs, g, eq⟩ := r.property
    exact ⟨sigs, mapGraph h g, (lower_map h g).symm.trans
      (congrArg (fun t => t.mapInstr (mapPrimitive h)) eq)⟩⟩

theorem GeneratedRegion.eval_map (r : GeneratedRegion P inputs out) (h : P ⟶ Q)
    (m : Model.{u, v, w} Q.op) (input : Tuple (Val m.value) (dataPorts inputs))
    (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Eval (instruction m) (inputEnv m input) (r.map h).val start label payload finish ↔
      Eval (instruction (reduct h m)) (inputEnv (reduct h m) input) r.val start label payload finish := by
  obtain ⟨_, g, eq⟩ := r.property
  simpa only [GeneratedRegion.map, ← eq] using eval_lower_map h g m input start finish label payload

def Equation.map (e : Equation P) (h : P ⟶ Q) : Equation Q :=
  ⟨e.inputs, e.out, e.lhs.map h, e.rhs.map h⟩

theorem Equation.map_id (e : Equation P) : e.map (𝟙 P) = e := by
  cases e
  simp only [map, GeneratedRegion.map, mapPrimitive_id, Isotope.LambdaSSA.Region.mapInstr_id]

theorem Equation.map_comp (e : Equation P) (h : P ⟶ Q) (k : Q ⟶ R) :
    e.map (h ≫ k) = (e.map h).map k := by
  cases e
  simp only [map, GeneratedRegion.map, mapPrimitive_comp, Isotope.LambdaSSA.Region.mapInstr_comp]

theorem Equation.satisfaction_map (e : Equation P) (h : P ⟶ Q) (m : Model.{u, v, w} Q.op) :
    (e.map h).Holds m ↔ e.Holds (reduct h m) := by
  simp only [Holds, map, GeneratedRegion.eval_map]
  rfl

theorem lowerEquation_map (e : Diamond.Institution.Equation P) (h : P ⟶ Q) :
    (lowerEquation e).map h = lowerEquation (e.map h) :=
  congrArg₂ (fun lhs rhs => (⟨e.inputs, e.out, lhs, rhs⟩ : Equation Q))
    (Subtype.ext (lower_map h e.lhs)) (Subtype.ext (lower_map h e.rhs))

/-- The lowered regions agree at every finite observation exactly when the
native equation holds in the inducing model. -/
theorem satisfaction (e : Diamond.Institution.Equation P) (m : Model.{u, v, w} P.op) :
    (lowerEquation e).Holds m ↔ e.Holds m :=
  Proofs.satisfaction e m

def corridor (h : P ⟶ Q) : room.{u, v, w} P ⟶ room.{u, v, w} Q :=
  ⟨fun e => e.map h, Diamond.Institution.reductFunctor h,
    fun m e => e.satisfaction_map h m.as⟩

theorem corridor_id (P : Diamond.Institution.Signature.{u, v} Data) :
    corridor.{u, v, w} (𝟙 P) = 𝟙 (room.{u, v, w} P) :=
  Room.hom_ext (funext Equation.map_id)
    (congrArg (fun f : Diamond.Institution.room.{u, v, w} P ⟶ _ => f.mod)
      (Diamond.Institution.corridor_id.{u, v, w} P))

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    corridor.{u, v, w} (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext fun e => e.map_comp h k)
    (congrArg (fun f : Diamond.Institution.room.{u, v, w} P ⟶ _ => f.mod)
      (Diamond.Institution.corridor_comp.{u, v, w} h k))

/-- The institution of generated λSSA observations indexed by the original
typed primitive signatures. -/
def inst (Data : Type u) :
    Inst.{max u (v + 1), max u v, max u v, max u v (w + 1), max u v (w + 1)} where
  Sign := Diamond.Institution.Signature.{u, v} Data
  I := ⟨room.{u, v, w}, corridor.{u, v, w}, corridor_id, corridor_comp⟩

def comparisonCorridor (P : Diamond.Institution.Signature.{u, v} Data) :
    Diamond.Institution.room.{u, v, w} P ⟶ room.{u, v, w} P :=
  ⟨lowerEquation, 𝟭 _, fun m e => satisfaction e m.as⟩

theorem comparison_natural (h : P ⟶ Q) :
    Diamond.Institution.corridor.{u, v, w} h ≫ comparisonCorridor Q =
      comparisonCorridor P ≫ corridor h :=
  Room.hom_ext (funext fun e => (lowerEquation_map e h).symm)
    (Discrete.functor_ext fun _ => rfl)

/-- The native diamond equations map into the generated λSSA equation
institution using the induced interpretation of each native model. -/
def comparison (Data : Type u) :
    Inst.CoHom (Diamond.Institution.inst.{u, v, w} Data) (inst.{u, v, w} Data) where
  Φ := 𝟭 _
  ρ := { app := comparisonCorridor
         naturality := fun {P Q} h => comparison_natural (P := P) (Q := Q) h }

end Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution
