module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms
public import Silmaril.Logic.Institution.Syntactic.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Correspondence

/-! Satisfaction and naturality in the matched source and CFG models. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution

open CategoryTheory Silmaril.Logic.Institution
open Diamond (Val dataPorts)
open RVSDG (Tuple)
open SeaOfNodes.MLIR (Word sourceInputs)
open Silmaril.MLIR.Arith (Env Width)

variable {B : Profile} {S T U : Signature}
variable {P Q R : Diamond.Institution.Signature.{0, 0} Width}

@[simp] theorem sourceInputs_encodeInput {Γ : List Width} (input : Tuple (Val Word) (dataPorts (inputSorts Γ))) :
    sourceInputs (encodeInput input) = input :=
  Proofs.sourceInputs_encodeInput input

@[simp] theorem encodeInput_sourceInputs {Γ : List Width} (input : Env Γ) :
    encodeInput (sourceInputs input) = input :=
  Proofs.encodeInput_sourceInputs input

@[simp] theorem SourceSentence.map_id (s : SourceSentence B P) : s.map (𝟙 P) = s :=
  Subtype.ext s.val.map_id

theorem SourceSentence.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (s : SourceSentence B P) :
    s.map (h ≫ k) = (s.map h).map k :=
  Subtype.ext (s.val.map_comp h k)

theorem model_reduct (f : S ⟶ T) :
    Diamond.Institution.reduct f.left (sourceModel T) = sourceModel S :=
  Proofs.model_reduct f

theorem translate_map (f : S ⟶ T) (s : SourceSentence B S.left) :
    translate T (s.map f.left) = translate S s :=
  Proofs.translate_map f s

/-- Exact partial observation at an encoded input, including undefinedness. -/
theorem translateProgram_observe (S : Signature)
    (g : Loop.Institution.Program S.left (inputSorts B.inputs) (.data B.result))
    (oneLatch : g.carried = [.data B.carried])
    (input : Tuple (Val Word) (dataPorts (inputSorts B.inputs))) :
    observe (translateProgram S g oneLatch) (encodeInput input) =
      (g.graph.denote (sourceModel S) input).map encodeResult :=
  Proofs.translateProgram_observe S g oneLatch input

theorem equation_at_iff (S : Signature)
    (lhs rhs : Loop.Institution.Program S.left (inputSorts B.inputs) (.data B.result))
    (leftLatch : lhs.carried = [.data B.carried]) (rightLatch : rhs.carried = [.data B.carried])
    (input : Tuple (Val Word) (dataPorts (inputSorts B.inputs))) :
    observe (translateProgram S lhs leftLatch) (encodeInput input) =
        observe (translateProgram S rhs rightLatch) (encodeInput input) ↔
      lhs.graph.denote (sourceModel S) input = rhs.graph.denote (sourceModel S) input := by
  rw [translateProgram_observe, translateProgram_observe]
  exact Proofs.map_encodeResult_eq_iff _ _

theorem observe_none_iff (S : Signature)
    (g : Loop.Institution.Program S.left (inputSorts B.inputs) (.data B.result))
    (oneLatch : g.carried = [.data B.carried])
    (input : Tuple (Val Word) (dataPorts (inputSorts B.inputs))) :
    observe (translateProgram S g oneLatch) (encodeInput input) = Part.none ↔
      g.graph.denote (sourceModel S) input = Part.none := by
  rw [translateProgram_observe, Part.eq_none_iff', Part.eq_none_iff']
  rfl

/-- Preservation and reflection for both admitted native sentence forms. -/
theorem satisfaction_induced (S : Signature) (s : SourceSentence B S.left) :
    (translate S s).Holds ↔ s.val.Holds (sourceModel S) :=
  Proofs.satisfaction_induced S s

@[expose] def sourceCorridor (B : Profile) (f : S ⟶ T) : sourceRoom B S ⟶ sourceRoom B T :=
  ⟨SourceSentence.map f.left, 𝟭 _, fun _ s =>
    (s.val.satisfaction f.left (sourceModel T)).trans
      (iff_of_eq (congrArg s.val.Holds (model_reduct f)))⟩

theorem sourceCorridor_id (B : Profile) (S : Signature) :
    sourceCorridor B (𝟙 S) = 𝟙 (sourceRoom B S) :=
  Room.hom_ext (funext SourceSentence.map_id) rfl

theorem sourceCorridor_comp (B : Profile) (f : S ⟶ T) (g : T ⟶ U) :
    sourceCorridor B (f ≫ g) = sourceCorridor B f ≫ sourceCorridor B g :=
  Room.hom_ext (funext (SourceSentence.map_comp f.left g.left)) rfl

@[expose] def sourceInst (B : Profile) : Inst.{1, 0, 0, 0, 0} where
  Sign := Signature
  I := ⟨sourceRoom B, sourceCorridor B, sourceCorridor_id B, sourceCorridor_comp B⟩

@[expose] def targetInst (B : Profile) : Inst.{0, 0, 0, 0, 0} :=
  Syntactic.oneSignature (targetRoom B)

/-- Each source room compares with the same concrete target room. -/
@[expose] def compare (B : Profile) (S : Signature) : sourceRoom B S ⟶ targetRoom B :=
  ⟨translate S, 𝟭 _, fun _ s => satisfaction_induced S s⟩

theorem compare_natural (B : Profile) (f : S ⟶ T) :
    sourceCorridor B f ≫ compare B T = compare B S ≫ 𝟙 (targetRoom B) :=
  Room.hom_ext (funext (translate_map f)) rfl

/-- A comorphism for the realized signatures and their matched models. -/
@[expose] def comorphism (B : Profile) : Inst.CoHom (sourceInst B) (targetInst B) where
  Φ := (Functor.const Signature).obj (Discrete.mk ())
  ρ := { app := compare B, naturality := fun _ _ f => compare_natural B f }

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution
