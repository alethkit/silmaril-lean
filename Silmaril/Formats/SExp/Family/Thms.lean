module

public import Silmaril.Formats.SExp.Family.Defs
import Silmaril.Proofs.Formats.SExp.Family.Basic

/-!
# Tree families: laws

* `SExp.toAST` is injective, lands in the well-arity trees, and `AST.toSExp` inverts it there:
  proper S-expressions are exactly the well-arity trees of `sexpSig` (`SExp.equivAST`);
* a leaf with a child is not a well-arity tree (`leaf_children_not_wellArity`): the arity
  predicate is what separates atoms from internal nodes;
* `HintedSExp.toSpki` is injective: hinted S-expressions embed in the RFC 9804 data model.
-/

@[expose] public section

namespace Silmaril.Formats

variable {α : Type}

@[simp] theorem SExp.toSExp_toAST (e : SExp α) : (SExp.toAST e).toSExp = e :=
  Silmaril.Proofs.Formats.SExp.Family.toSExp_toAST e

theorem SExp.toAST_wellArity (e : SExp α) : AST.WellArity (SExp.toAST e) :=
  Silmaril.Proofs.Formats.SExp.Family.toAST_wellArity e

theorem AST.toAST_toSExp {x : AST (sexpSig α)} (h : AST.WellArity x) :
    SExp.toAST x.toSExp = x :=
  Silmaril.Proofs.Formats.SExp.Family.toAST_toSExp x h

theorem SExp.toAST_injective : Function.Injective (SExp.toAST : SExp α → AST (sexpSig α)) :=
  Silmaril.Proofs.Formats.SExp.Family.toAST_injective

/-- **Proper S-expressions are the well-arity `sexpSig` trees.** -/
def SExp.equivAST (α : Type) : SExp α ≃ {x : AST (sexpSig α) // AST.WellArity x} where
  toFun e := ⟨SExp.toAST e, SExp.toAST_wellArity e⟩
  invFun x := x.1.toSExp
  left_inv e := SExp.toSExp_toAST e
  right_inv x := Subtype.ext (AST.toAST_toSExp x.2)

theorem leaf_children_not_wellArity (a : α) (c : AST (sexpSig α)) :
    ¬ AST.WellArity (AST.node (S := sexpSig α) SxTag.leaf a [c]) :=
  Silmaril.Proofs.Formats.SExp.Family.leaf_children_not_wellArity a c

theorem HintedSExp.toSpki_injective : Function.Injective HintedSExp.toSpki :=
  Silmaril.Proofs.Formats.SExp.Family.toSpki_injective

end Silmaril.Formats
