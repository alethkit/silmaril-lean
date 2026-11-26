module

public import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted.Correspondence

/-! Native reducts for the restricted scoped image diagram. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted

open CategoryTheory Silmaril.Logic.Institution

variable {Data : Type} {P Q R : Diamond.Institution.Signature.{0, 0} Data}

/-- Changing carrier encodings gives the original model back when undone. -/
theorem transport_inverse {S : Silmaril.MLIR.Institution.Signature true}
    (M : Silmaril.MLIR.Institution.Model S) {value : S.Ty → Type}
    (encode : ∀ t, M.carrier t ≃ value t) :
    transport (transport M encode) (fun t => (encode t).symm) = M :=
  Proofs.transport_inverse M encode

/-- In canonical carriers an admitted model is exactly the model induced by extraction. -/
theorem normalize_eq_induced (M : Model P) :
    M.toPresentation.normalize = Diamond.MLIR.model M.extract :=
  Proofs.normalize_eq_induced M

/-- The translation satisfies the comorphism law for an admitted model and its native reduct. -/
theorem satisfaction (M : Model P) (e : Diamond.Institution.Equation P) :
    (translate e).Holds M.base ↔ e.Holds M.extract :=
  Proofs.satisfaction M e

theorem extract_reduct (h : P ⟶ Q) (M : Model Q) :
    (M.reduct h).extract = Diamond.Institution.reduct h M.extract :=
  Proofs.extract_reduct h M

theorem reduct_id (M : Model P) : M.reduct (𝟙 P) = M :=
  Proofs.reduct_id M

theorem reduct_comp (h : P ⟶ Q) (k : Q ⟶ R) (M : Model R) :
    M.reduct (h ≫ k) = (M.reduct k).reduct h :=
  Proofs.reduct_comp h k M

/-- Scoped sentences and admitted scoped models, indexed by the generating native signature. -/
@[expose] def room (P : Diamond.Institution.Signature.{0, 0} Data) : Room.{0, 1, 1} where
  Sen := Silmaril.MLIR.Institution.Equation (target P)
  Mod := Cat.of (Discrete (Model P))
  Sat M e := e.Holds M.as.base

@[expose] def corridor (h : P ⟶ Q) : room P ⟶ room Q :=
  ⟨fun e => e.map (scopedMap h), Discrete.functor (fun M => Discrete.mk (M.reduct h)),
    fun M e => Silmaril.MLIR.Institution.satisfaction (scopedMap h) M.as.base e⟩

theorem corridor_id (P : Diamond.Institution.Signature.{0, 0} Data) :
    corridor (𝟙 P) = 𝟙 (room P) := by
  apply Room.hom_ext
  · have h : scopedMap (𝟙 P) = 𝟙 (target P) := (signatureFunctor Data).map_id P
    exact funext fun e => (congrArg (fun f => e.map f) h).trans e.map_id
  · exact Discrete.functor_ext fun M => congrArg Discrete.mk (reduct_id M)

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    corridor (h ≫ k) = corridor h ≫ corridor k := by
  apply Room.hom_ext
  · have hk : scopedMap (h ≫ k) = scopedMap h ≫ scopedMap k :=
      (signatureFunctor Data).map_comp h k
    exact funext fun e => (congrArg (fun f => e.map f) hk).trans (e.map_comp _ _)
  · exact Discrete.functor_ext fun M => congrArg Discrete.mk (reduct_comp h k M)

/-- The scoped image institution over generating signatures, restricted to admitted models. -/
@[expose] def inst (Data : Type) : Inst.{1, 0, 0, 1, 1} where
  Sign := Diamond.Institution.Signature.{0, 0} Data
  I := ⟨room, corridor, corridor_id, corridor_comp⟩

/-- Lower sentences forwards and extract native models backwards over the scoped image diagram. -/
@[expose] def comorphism (Data : Type) :
    Inst.CoHom (Diamond.Institution.inst.{0, 0, 0} Data) (inst Data) where
  Φ := 𝟭 _
  ρ :=
    { app := fun _ =>
        ⟨translate, Discrete.functor (fun M : Model _ => Discrete.mk M.extract),
          fun M e => satisfaction M.as e⟩
      naturality := fun _ _ h => Room.hom_ext (funext (translate_map h))
        (Discrete.functor_ext fun M => congrArg Discrete.mk (extract_reduct h M).symm) }

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted
