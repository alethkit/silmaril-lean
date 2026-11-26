module

public import Silmaril.SSA.Isotope.Institution.Ordered.Thms

/-! # A fresh undefined-behaviour symbol in each judgment sort -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Refinement.UB

open CategoryTheory Limits
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel

universe u v

/-- Adjoin a literal nullary operation at each sort. The old operations keep their arities
and argument sorts. A contextual typing sort includes the input context and result type. -/
abbrev signature {I : Type u} (S : TheoryModel.Signature.{u,v} I) : TheoryModel.Signature.{u,v} I where
  Op i := Option (S.Op i)
  arity := fun {_} o => match o with
    | none => 0
    | some o => S.arity o
  argSort := fun {_} o => match o with
    | none => Fin.elim0
    | some o => S.argSort o

/-- Explicit syntax with a separate UB constructor, using the original operations as nodes. -/
inductive Expr {I : Type u} (S : TheoryModel.Signature.{u,v} I) : I → Type (max u v)
  | ub {i : I} : Expr S i
  | node {i : I} (o : S.Op i) (args : (j : Fin (S.arity o)) → Expr S (S.argSort o j)) : Expr S i

variable {I : Type u} {S : TheoryModel.Signature.{u,v} I}

/-- The constructor algebra for the extended signature. -/
def syntaxAlgebra (S : TheoryModel.Signature.{u,v} I) : Algebra.{u,v,max u v} (signature S) where
  Carrier := Expr S
  op := fun {_} o => match o with
    | none => fun _ => .ub
    | some o => .node o

/-- Interpret explicit UB as the new constant in an arbitrary extended algebra. -/
def fold (M : Algebra.{u,v,max u v} (signature S)) : {i : I} → Expr S i → M.Carrier i
  | _, .ub => M.op none (fun j => Fin.elim0 j)
  | _, .node o args => M.op (some o) (fun j => fold M (args j))

/-- The fold as an operation homomorphism. -/
def foldHom (M : Algebra.{u,v,max u v} (signature S)) : syntaxAlgebra S ⟶ M where
  map := fold M
  comm := fun {_} o => match o with
    | none => fun _ => congrArg (M.op none) (funext fun j => Fin.elim0 j)
    | some _ => fun _ => rfl


end Silmaril.Isotope.Institution.Refinement.UB
