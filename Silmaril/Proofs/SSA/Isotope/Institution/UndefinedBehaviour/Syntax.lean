module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Syntax.Defs

public section

namespace Silmaril.Proofs.Isotope.Institution.Refinement.UB

open CategoryTheory Limits Silmaril.Isotope.Institution.Refinement.UB
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel

universe u v

noncomputable def syntaxIsInitial {I : Type u} (S : TheoryModel.Signature.{u,v} I) :
    IsInitial (syntaxAlgebra S) := by
  refine IsInitial.ofUniqueHom (fun M => foldHom M) ?_
  intro M f
  apply Algebra.Hom.ext
  intro i t
  induction t with
  | ub =>
    exact (f.comm none (fun j => Fin.elim0 j)).trans
      (congrArg (M.op none) (funext fun j => Fin.elim0 j))
  | node o args ih =>
    exact (f.comm (some o) args).trans (congrArg (M.op (some o)) (funext ih))

end Silmaril.Proofs.Isotope.Institution.Refinement.UB
