module

public import Silmaril.SSA.MLIR.Institution.Syntax.Observational.Products.Defs
import Silmaril.Proofs.SSA.MLIR.Institution.Syntax.Observational.Products.Laws

public section

namespace Silmaril.MLIR.Institution.Syntax.Observational

open CategoryTheory Limits

variable {withRegions : Bool} {S : Signature withRegions} {models : Model S → Prop}
variable {W X Y : Context models}

/-- The empty context is terminal. -/
def emptyIsTerminal (models : Model S → Prop) : IsTerminal (empty models) :=
  IsTerminal.ofUniqueHom (fun _ => ofBlock (fun i => Fin.elim0 i))
    (fun _ => Proofs.MLIR.Institution.Syntax.Observational.empty_unique)

/-- Pair quotient arrows by concatenating the result slots of their representatives. -/
def pair (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ append X Y :=
  Quotient.liftOn₂ f g (fun a b => ofBlock (pairBlocks a b))
    (fun _ _ _ _ ha hb =>
      Quotient.sound (Proofs.MLIR.Institution.Syntax.Observational.pairBlocks_rel ha hb))

@[simp] theorem pair_comp_fst (f : W ⟶ X) (g : W ⟶ Y) : pair f g ≫ fst X Y = f :=
  Quotient.inductionOn₂ f g Proofs.MLIR.Institution.Syntax.Observational.pair_fst

@[simp] theorem pair_comp_snd (f : W ⟶ X) (g : W ⟶ Y) : pair f g ≫ snd X Y = g :=
  Quotient.inductionOn₂ f g Proofs.MLIR.Institution.Syntax.Observational.pair_snd

/-- An arrow into a concatenated context is determined by its two projections. -/
theorem append_hom_ext {f g : W ⟶ append X Y}
    (hl : f ≫ fst X Y = g ≫ fst X Y) (hr : f ≫ snd X Y = g ≫ snd X Y) : f = g :=
  Proofs.MLIR.Institution.Syntax.Observational.append_hom_ext hl hr

/-- Concatenation with its slot projections is a binary product. -/
def binaryFanIsLimit (X Y : Context models) : IsLimit (binaryFan X Y) :=
  BinaryFan.IsLimit.mk _ pair pair_comp_fst pair_comp_snd
    (fun f g _ hl hr =>
      append_hom_ext (hl.trans (pair_comp_fst f g).symm) (hr.trans (pair_comp_snd f g).symm))

instance : HasFiniteProducts (Context models) :=
  letI : HasTerminal (Context models) := (emptyIsTerminal models).hasTerminal
  letI {X Y : Context models} : HasLimit (Limits.pair X Y) :=
    HasLimit.mk ⟨binaryFan X Y, binaryFanIsLimit X Y⟩
  letI : HasBinaryProducts (Context models) := hasBinaryProducts_of_hasLimit_pair (Context models)
  hasFiniteProducts_of_has_binary_and_terminal

end Silmaril.MLIR.Institution.Syntax.Observational
