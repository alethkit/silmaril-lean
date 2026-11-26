module

public import Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.Theta.Institution.Correspondence

/-! The numbered θ lowering preserves and reflects partial loop sentences in induced models. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG.NestedTheta.Institution
open Diamond (Ty Val ValueSort dataPorts)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P Q R : Diamond.Institution.Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}

theorem signatureMap_id (P : Diamond.Institution.Signature.{u, v} Data) :
    signatureMap (𝟙 P) = 𝟙 (target P) :=
  Proofs.signatureMap_id P

theorem signatureMap_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    signatureMap (h ≫ k) = signatureMap h ≫ signatureMap k :=
  Proofs.signatureMap_comp h k

/-- Signature translation into the existing typed RVSDG signature category. -/
@[expose] def signatureFunctor (Data : Type u) :
    Diamond.Institution.Signature.{u, v} Data ⥤ RVSDG.Institution.Signature.{u, max u v} (ValueSort Data) PEmpty.{u + 1} :=
  ⟨target, signatureMap, signatureMap_id, signatureMap_comp⟩

theorem lowerTheta_map (h : P ⟶ Q) (g : Graph P.op inputs carried entrySigs headerSigs out) :
    (Loop.Institution.mapGraph h g).lowerTheta = RVSDG.NestedTheta.Institution.mapGraph (opcodeMap h) g.lowerTheta :=
  Proofs.lowerTheta_map h g

theorem translate_map (h : P ⟶ Q) (s : Loop.Institution.Sentence P) :
    translate (s.map h) = (translate s).map (signatureMap h) :=
  Proofs.translate_map h s

/-- The induced runtime model commutes with reduct, including the readback
interpretation that re-evaluates the relabelled header table. -/
theorem model_reduct (h : P ⟶ Q) (m : Diamond.Model.{u, v, w} Q.op) :
    RVSDG.Institution.reduct (opcodeMap h) (thetaRuntime m) = thetaRuntime (Diamond.Institution.reduct h m) :=
  Proofs.model_reduct h m

/-- The actual target observation is the native partial value in a singleton tuple. -/
theorem lowerTheta_observe (g : Graph P.op inputs carried entrySigs headerSigs out)
    (m : Diamond.Model.{u, v, w} P.op) (input : Tuple (Val m.value) (dataPorts inputs)) :
    RuntimeObservation.observe (thetaRuntime m) g.lowerTheta input =
      (g.denote m input).map (fun result => .cons result .nil) :=
  Proofs.lowerTheta_observe g m input

/-- Both partial equations and universal termination are preserved and reflected. -/
theorem satisfaction_induced (s : Loop.Institution.Sentence P) (m : Diamond.Model.{u, v, w} P.op) :
    (translate s).Holds (thetaRuntime m) ↔ s.Holds m :=
  Proofs.satisfaction_induced s m

/-- Forward sentence translation commutes with signature relabelling. -/
@[expose] def sentenceTranslation (Data : Type u) :
    sentenceFunctor (Loop.Institution.inst.{u, v, w} Data).I ⟶
      signatureFunctor Data ⋙ sentenceFunctor (RuntimeObservation.inst.{u, max u v, w} (ValueSort Data) PEmpty).I where
  app _ := TypeCat.ofHom translate
  naturality _ _ h := congrArg TypeCat.ofHom (funext (translate_map h))

/-- Model induction runs forward, naturally in the two contravariant model functors. -/
@[expose] def inducedModels (Data : Type u) :
    modelFunctor (Loop.Institution.inst.{u, v, w} Data).I ⟶
      (signatureFunctor Data).op ⋙ modelFunctor (RuntimeObservation.inst.{u, max u v, w} (ValueSort Data) PEmpty).I where
  app P := (Discrete.functor fun m : Diamond.Model.{u, v, w} P.unop.op => Discrete.mk (thetaRuntime m)).toCatHom
  naturality _ _ h := congrArg Functor.toCatHom
    (Discrete.functor_ext fun m => congrArg Discrete.mk (model_reduct h.unop m).symm)

end Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution
