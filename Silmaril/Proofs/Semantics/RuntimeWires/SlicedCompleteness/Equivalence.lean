module

public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Quotient
public import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Interpretation
public import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Decoding

public section

namespace Silmaril.RuntimeWires.Proofs.SlicedCompleteness

open CategoryTheory Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {A B C X Y : List O}

theorem representable (E : Diagram.Equations S) (f : Diagram.Hom S E A B) :
    ∃ p : Sheet S A B, p.denote E = f :=
  Quotient.inductionOn f fun t => ⟨Sheet.encode t, denote_encode E t⟩

theorem from_to (f : SeamHom S A B) : SeamHom.fromTermHom (f.toTermHom) = f := by
  refine Quotient.inductionOn f fun p => ?_
  change SeamHom.fromTermHom (p.denote (noEquations S)) = SeamHom.ofSheet p
  rw [← sheetTerm_denote (noEquations S) p]
  exact Quotient.sound (encode_sheet p)

theorem to_from (f : Diagram.Hom S (noEquations S) A B) :
    (SeamHom.fromTermHom f).toTermHom = f :=
  Quotient.inductionOn f (denote_encode (noEquations S))

theorem toTerm_comp (f : SeamHom S A B) (g : SeamHom S B C) :
    (f.comp g).toTermHom =
      ((show (⟨A⟩ : Diagram.Presented S (noEquations S)) ⟶ ⟨B⟩ from f.toTermHom) ≫
        (show (⟨B⟩ : Diagram.Presented S (noEquations S)) ⟶ ⟨C⟩ from g.toTermHom)) :=
  Quotient.inductionOn₂ f g (denote_then (noEquations S))

theorem toTerm_tensor (f : SeamHom S A B) (g : SeamHom S X Y) :
    (f.tensor g).toTermHom =
      Diagram.Presented.tensorMap
        (show (⟨A⟩ : Diagram.Presented S (noEquations S)) ⟶ ⟨B⟩ from f.toTermHom)
        (show (⟨X⟩ : Diagram.Presented S (noEquations S)) ⟶ ⟨Y⟩ from g.toTermHom) :=
  Quotient.inductionOn₂ f g (denote_tensor (noEquations S))

end Silmaril.RuntimeWires.Proofs.SlicedCompleteness
