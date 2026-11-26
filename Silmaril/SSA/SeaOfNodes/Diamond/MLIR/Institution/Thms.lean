module

public import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms
public import Silmaril.SSA.MLIR.Institution.Thms
public import Silmaril.SSA.RVSDG.MLIR.Graph.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.MLIR.Institution.Naturality

/-! Naturality of scoped lowering and induced models over native diamond signatures. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution

open CategoryTheory Silmaril.Logic.Institution

variable {Data : Type} {P Q R : Diamond.Institution.Signature.{0, 0} Data}

theorem rvsdgMap_id (P : Diamond.Institution.Signature.{0, 0} Data) :
    rvsdgMap (𝟙 P) = 𝟙 (source P.op) :=
  Proofs.rvsdgMap_id P

theorem rvsdgMap_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    rvsdgMap (h ≫ k) = rvsdgMap h ≫ rvsdgMap k :=
  Proofs.rvsdgMap_comp h k

/-- The generated RVSDG signatures form a functor on native diamond signatures. -/
@[expose] def rvsdgSignatureFunctor (Data : Type) :
    Diamond.Institution.Signature.{0, 0} Data ⥤ RVSDG.MLIR.Graph.Source (ValueSort Data) where
  obj P := source P.op
  map := rvsdgMap
  map_id := rvsdgMap_id
  map_comp := rvsdgMap_comp

/-- The scoped signature functor factors through the existing RVSDG signature functor. -/
@[expose] def signatureFunctor (Data : Type) :
    (Diamond.Institution.inst.{0, 0, 0} Data).Sign ⥤ Silmaril.MLIR.Institution.Signature true :=
  rvsdgSignatureFunctor Data ⋙ RVSDG.MLIR.Graph.signatureFunctor (ValueSort Data)

/-- The numbered RVSDG lowering commutes with the native opcode renaming. -/
theorem rvsdg_lower_map (h : P ⟶ Q) {inputs : List (ValueSort Data)}
    {sigs : List (List (Diamond.Ty Data))} {out : ValueSort Data} (g : Graph P.op inputs sigs out) :
    (Diamond.Institution.mapGraph h g).lower =
      RVSDG.Institution.mapGraph (opcodeMap h) g.lower :=
  Proofs.rvsdg_lower_map h g

/-- Lowering to a scoped block commutes with source relabelling at each result slot. -/
theorem lower_map (h : P ⟶ Q) {inputs : List (ValueSort Data)}
    {sigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}
    (g : Graph P.op inputs sigs out) (i : Fin 1) :
    lower (Diamond.Institution.mapGraph h g) i = (lower g i).map ((signatureFunctor Data).map h) :=
  Proofs.lower_map h g i

/-- Sentence translation is natural along the scoped signature functor. -/
theorem translate_map (h : P ⟶ Q) (e : Diamond.Institution.Equation P) :
    translate (e.map h) = (translate e).map ((signatureFunctor Data).map h) :=
  Proofs.translate_map h e

/-- Reducing a scoped model induced by a diamond model agrees with inducing the reduct. -/
theorem model_reduct (h : P ⟶ Q) (m : Model.{0, 0, 0} Q.op) :
    (model m).reduct ((signatureFunctor Data).map h) = model (Diamond.Institution.reduct h m) :=
  Proofs.model_reduct h m

/-- Satisfaction is preserved and reflected in the scoped model induced by a source model. -/
theorem satisfaction_induced (e : Diamond.Institution.Equation P) (m : Model.{0, 0, 0} P.op) :
    (translate e).Holds (model m) ↔ e.Holds m :=
  Diamond.MLIR.satisfaction m e.lhs e.rhs

/-- Sentence translation between the existing institutions' sentence functors. -/
@[expose] def sentenceTranslation (Data : Type) :
    sentenceFunctor (Diamond.Institution.inst.{0, 0, 0} Data).I ⟶
      signatureFunctor Data ⋙ sentenceFunctor (Silmaril.MLIR.Institution.institution (withRegions := true)) where
  app _ := TypeCat.ofHom translate
  naturality _ _ h := congrArg TypeCat.ofHom (funext (translate_map h))

/-- Model induction runs from source to target, naturally in both institutions' reducts. -/
@[expose] def inducedModels (Data : Type) :
    modelFunctor (Diamond.Institution.inst.{0, 0, 0} Data).I ⟶
      (signatureFunctor Data).op ⋙ modelFunctor (Silmaril.MLIR.Institution.institution (withRegions := true)) where
  app P := (Discrete.functor fun m : Model.{0, 0, 0} P.unop.op => Discrete.mk (model m)).toCatHom
  naturality _ _ h := congrArg Functor.toCatHom
    (Discrete.functor_ext fun m => congrArg Discrete.mk (model_reduct h.unop m).symm)

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution
