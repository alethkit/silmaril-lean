module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Defs

/-! # Native dispatcher of a positional table -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional

open CategoryTheory CategoryTheory.Limits
open Silmaril.SSA.RVSDG.LambdaSSA
open LinearChain.Categorical (siteArrow cfgStepOf localInject)
open LambdaSSA.Semantics.Categorical (labelInject labelObj)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w h k

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  {n : Nat} {L : LCtx τ}

noncomputable def Table.blockArrows (p : Table Φ L n) (i : Fin n) :
    J.obj (M.obj (p.types i)) ⟶ J.obj (labelObj M (List.ofFn p.types ++ L)) :=
  Acyclic.Categorical.blockArrow J M (fun _ s => J.map (siteArrow M s)) (p.block i)

noncomputable def Table.step (p : Table Φ L n) :=
  cfgStepOf J M p.types L (p.blockArrows J M)

/-- Enter the native feedback dispatcher at the specified local label. -/
noncomputable def Table.resultAt [Iteration C] (p : Table Φ L n) (i : Fin n) :
    J.obj (M.obj (p.types i)) ⟶ J.obj (labelObj M L) :=
  J.map (localInject M p.types i) ≫ iterate (p.step J M)

/-- A local transfer continues in the dispatcher. An outward transfer
uses the original positional coproduct injection. -/
noncomputable def Destination.result [Iteration C] {p : Table Φ L n} {A : τ} :
    Destination p A → (J.obj (M.obj A) ⟶ J.obj (labelObj M L))
  | .local i ty => ty ▸ p.resultAt J M i
  | .exit j ty => J.map (labelInject M j ty)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional
