module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.FiniteExitCategorical

/-! # Packing the native denotation of structured acyclic regions -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit

open CategoryTheory CategoryTheory.Limits
open Region (packedExitType)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent denoteRegion packLabelExit unpackLabelExit
  packLabelExit_unpackLabelExit unpackLabelExit_packLabelExit)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

/-- The nested sum encoding postcomposes the actual native positional
denotation with the label packing isomorphism. -/
theorem denote_encode {L : LCtx τ} {n : Nat} {β : BoundCtx τ n} (c : FiniteExit Φ L β) :
    denoteRegion J M (c.encode.toSSA_hasType (L := [packedExitType L]) (exit := 0) rfl) =
      denoteRegion J M c.toSSA_hasType ≫ J.map (packLabelExit M L) :=
  denote_encode_proof J M c

/-- Decoding a tagged result at a nonempty interface applies the inverse
label map in the actual native positional semantics. -/
theorem denote_decode {L : LCtx τ} {n : Nat} {β : BoundCtx τ n} (hne : L ≠ [])
    (c : Code Φ β (packedExitType L)) :
    denoteRegion J M (decode hne c).toSSA_hasType =
      denoteRegion J M (c.toSSA_hasType (L := [packedExitType L]) (exit := 0) rfl) ≫
        J.map (unpackLabelExit M L) :=
  denote_decode_proof J M hne c

/-- Encoding followed by decoding preserves every native denotation. -/
theorem denote_decode_encode {L : LCtx τ} {n : Nat} {β : BoundCtx τ n} (c : FiniteExit Φ L β) :
    denoteRegion J M (decode c.exits_ne_nil c.encode).toSSA_hasType =
      denoteRegion J M c.toSSA_hasType := by
  rw [denote_decode J M, denote_encode J M, Category.assoc, ← J.map_comp,
    packLabelExit_unpackLabelExit, J.map_id, Category.comp_id]

/-- With the exit list selected, decoding and encoding preserve the packed
arrow in the same coherent model. -/
theorem denote_encode_decode {L : LCtx τ} {n : Nat} {β : BoundCtx τ n} (hne : L ≠ [])
    (c : Code Φ β (packedExitType L)) :
    denoteRegion J M ((decode hne c).encode.toSSA_hasType (L := [packedExitType L]) (exit := 0) rfl) =
      denoteRegion J M (c.toSSA_hasType (L := [packedExitType L]) (exit := 0) rfl) := by
  rw [denote_encode J M, denote_decode J M, Category.assoc, ← J.map_comp,
    unpackLabelExit_packLabelExit, J.map_id, Category.comp_id]

end Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit

namespace Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit

open CategoryTheory CategoryTheory.Limits
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical (denoteRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- The finite-exit specialization has the same native computation arrow
as the binary bridge. The two encoders can use different sum types. -/
theorem denote_toFinite {A B : τ} {n : Nat} {β : BoundCtx τ n} (c : TwoExit Φ A B β) :
    denoteRegion J M c.toFinite.toSSA_hasType = denoteRegion J M c.toSSA_hasType :=
  FiniteExit.denote_toFinite_proof J M c

end Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit
