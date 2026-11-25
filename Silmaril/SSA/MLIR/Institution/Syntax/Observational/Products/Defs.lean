module

public import Silmaril.SSA.MLIR.Institution.Syntax.Observational.Defs
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! Chosen products of observational contexts. -/

@[expose] public section

namespace Silmaril.MLIR.Institution.Syntax.Observational

open CategoryTheory Limits

variable {withRegions : Bool} {S : Signature withRegions} {models : Model S → Prop}
variable {W X Y : Context models}

/-- The context with zero slots. -/
def empty (models : Model S → Prop) : Context models :=
  ⟨⟨0, Fin.elim0⟩⟩

/-- Concatenate the ordered slots of two contexts. -/
abbrev append (X Y : Context models) : Context models :=
  ⟨⟨X.raw.length + Y.raw.length, Fin.addCases X.raw.ty Y.raw.ty⟩⟩

theorem append_left (X Y : Context models) (i : Fin X.raw.length) :
    (append X Y).raw.ty (i.castAdd Y.raw.length) = X.raw.ty i :=
  Fin.addCases_left (motive := fun _ => S.Ty) (left := X.raw.ty) (right := Y.raw.ty) i

theorem append_right (X Y : Context models) (i : Fin Y.raw.length) :
    (append X Y).raw.ty (i.natAdd X.raw.length) = Y.raw.ty i :=
  Fin.addCases_right (motive := fun _ => S.Ty) (left := X.raw.ty) (right := Y.raw.ty) i

/-- Project the first segment of a concatenated context. -/
def fst (X Y : Context models) : append X Y ⟶ X :=
  ofBlock fun i => append_left X Y i ▸ .var (i.castAdd Y.raw.length)

/-- Project the second segment of a concatenated context. -/
def snd (X Y : Context models) : append X Y ⟶ Y :=
  ofBlock fun i => append_right X Y i ▸ .var (i.natAdd X.raw.length)

def binaryFan (X Y : Context models) : BinaryFan X Y := BinaryFan.mk (fst X Y) (snd X Y)

/-- Pair raw blocks by concatenating their tuples of results. -/
def pairBlocks (f : W.raw ⟶ X.raw) (g : W.raw ⟶ Y.raw) : W.raw ⟶ (append X Y).raw :=
  Fin.addCases (fun i => (append_left X Y i).symm ▸ f i)
    (fun i => (append_right X Y i).symm ▸ g i)

end Silmaril.MLIR.Institution.Syntax.Observational
