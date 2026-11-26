module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Categorical.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TwoExitCategorical

/-! # Encoding and decoding in the native positional region semantics -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit

open CategoryTheory CategoryTheory.Limits
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent denoteRegion labelObj)

variable {τ : Type u} [TypeFormers τ] {A B : τ}
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V)

@[simp] theorem packExit_unpackExit : packExit M A B ≫ unpackExit M A B = 𝟙 _ :=
  packExit_unpackExit_proof M

@[simp] theorem unpackExit_packExit : unpackExit M A B ≫ packExit M A B = 𝟙 _ :=
  unpackExit_packExit_proof M

/-- The binary tag identifies the original two-label coproduct with one
label carrying a coproduct payload. -/
noncomputable def exitIso (A B : τ) : labelObj M [A, B] ≅ labelObj M [coprod A B] where
  hom := packExit M A B
  inv := unpackExit M A B
  hom_inv_id := packExit_unpackExit M
  inv_hom_id := unpackExit_packExit M

variable {Φ : Type v} [HasTy Φ τ] {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  {n : Nat} {β : BoundCtx τ n}

/-- Encoding postcomposes the native two-label arrow with the coproduct
isomorphism. Both arrows are selected by the positional region semantics. -/
theorem denote_encode (c : TwoExit Φ A B β) :
    denoteRegion J M (c.encode.toSSA_hasType (L := [coprod A B]) (exit := 0) rfl) =
      denoteRegion J M c.toSSA_hasType ≫ J.map (packExit M A B) :=
  denote_encode_proof M J c

/-- The actual decoding CFG executes its binary dispatcher after computing
the tagged payload. -/
theorem denote_decode (c : Code Φ β (coprod A B)) :
    denoteRegion J M (decode c).toSSA_hasType =
      denoteRegion J M (c.toSSA_hasType (L := [coprod A B]) (exit := 0) rfl) ≫
        J.map (unpackExit M A B) :=
  denote_decode_proof M J c

/-- The native two-exit arrow is preserved by encoding and decoding. -/
theorem denote_decode_encode (c : TwoExit Φ A B β) :
    denoteRegion J M (decode c.encode).toSSA_hasType = denoteRegion J M c.toSSA_hasType := by
  rw [denote_decode M J, denote_encode M J, Category.assoc, ← J.map_comp,
    packExit_unpackExit, J.map_id, Category.comp_id]

end Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit
