module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TypeChange

/-! # The exact structured SSA institution over changing types -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Inst Room)
open Morphism (SignatureMap)
open LambdaSSA.Acyclic (Code Operand)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums]

@[simp] theorem mapSSASignature_id (e : SSAEquation P) :
    mapSSASignature (P := P) (Q := P) SignatureMap.id e = e :=
  mapSSASignature_id_proof e

theorem mapSSASignature_comp (e : SSAEquation P) :
    mapSSASignature (h.comp g) e = mapSSASignature h (mapSSASignature g e) :=
  mapSSASignature_comp_proof g h e

/-- Identity relabelling agrees with the original operand at the transported context. -/
theorem operandSignature_id_heq {n : Nat} {β : BoundCtx τ n} {A : τ} (a : Operand P.Instr β A) :
    HEq (a.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) a :=
  mapOperand_id a

/-- Composition of operand relabellings agrees after transport of the result type. -/
theorem operandSignature_comp_cast_heq {n : Nat} {β : BoundCtx τ n} {A : τ}
    (a : Operand P.Instr β A) {B : υ} {D : κ}
    (eg : g.ty A = B) (eh : h.ty B = D) (ec : (h.comp g).ty A = D) :
    HEq ((a.mapSignature (h.comp g)).castResult ec)
      ((((a.mapSignature g).castResult eg).mapSignature h).castResult eh) :=
  mapOperand_comp_cast g h a eg eh ec

/-- Composition of operand relabellings agrees at the mapped contexts. -/
theorem operandSignature_comp_heq {n : Nat} {β : BoundCtx τ n} {A : τ} (a : Operand P.Instr β A) :
    HEq (a.mapSignature (h.comp g)) ((a.mapSignature g).mapSignature h) :=
  mapOperand_comp g h a

/-- Identity relabelling preserves structured single-exit code. -/
theorem singleCodeSignature_id_heq {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code P.Instr β A) :
    HEq (c.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) c :=
  codeSignature_id_heq c

/-- Relabelling single-exit code along a composite agrees with relabelling twice. -/
theorem singleCodeSignature_comp_heq {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code P.Instr β A) :
    HEq (c.mapSignature (h.comp g)) ((c.mapSignature g).mapSignature h) :=
  codeSignature_comp_heq g h c

section Models

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

@[simp] theorem ssaSignatureCorridor_id :
    ssaSignatureCorridor (J := J) (P := P) (Q := P) SignatureMap.id = 𝟙 (ssaRoom J P) :=
  ssaSignatureCorridor_id_proof

theorem ssaSignatureCorridor_comp :
    ssaSignatureCorridor (J := J) (h.comp g) = ssaSignatureCorridor g ≫ ssaSignatureCorridor h :=
  ssaSignatureCorridor_comp_proof g h

/-- The new model functor restricts to the original primitive model functor. -/
theorem ssaSignatureCorridor_primitive_mod {P Q : InstrSig τ ε} (f : P ⟶ Q) :
    (ssaSignatureCorridor (J := J) f.toSignatureMap).mod = (ssaCorridor (J := J) f).mod :=
  ssaSignatureCorridor_primitive_mod_proof f

/-- The witnessed exact SSA corridor is functorial over type, effect, and
primitive changes that preserve the type formers. -/
noncomputable def ssaTypeInst (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : TypeSignature ⥤ Room.{0, 0, 1} where
  obj P := ssaRoom J P.prim
  map f := ssaSignatureCorridor f.signatureMap
  map_id _ := ssaSignatureCorridor_id
  map_comp f g := ssaSignatureCorridor_comp f.signatureMap g.signatureMap

/-- The bundled exact SSA institution over type-changing signatures. -/
noncomputable def ssaTypeInstitution (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : Inst.{1, 0, 0, 0, 1} :=
  ⟨TypeSignature, ssaTypeInst J⟩

end Models
end Silmaril.Isotope.Institution.Acyclic
