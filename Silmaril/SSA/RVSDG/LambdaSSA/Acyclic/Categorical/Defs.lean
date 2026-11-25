module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Lowering.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatcher.Defs

/-! # Premonoidal semantics of typed acyclic bodies and their CFG dispatchers -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaSSA.Semantics.Categorical (labelObj)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LinearChain (Site)
open LinearChain.Categorical (call choice cfgStepOf decodeLabels siteArrow)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable {A B : τ} {L R : List τ} {T : C}

abbrev LabelArrows (L : List τ) (T : C) := (X : τ) → Site L X → (J.obj (M.obj X) ⟶ T)

/-- The abstract γ semantics binds the typed payload of the selected
coproduct injection. Branch targets need not be central. -/
noncomputable def denote : {A B : τ} → Body Φ A B → (J.obj (M.obj A) ⟶ J.obj (M.obj B))
  | _, _, .instruction op => call J M op
  | _, _, .sequence first next => denote first ≫ denote next
  | _, _, .choice op l r => choice J M op ≫ coprod.desc (denote l) (denote r)

/-- The numbered term is admitted structurally. At γ the sum and its
matching selector are interpreted as one coproduct. -/
noncomputable def denoteForm {term : RVBody Φ A B} :
    Form A B term → (J.obj (M.obj A) ⟶ J.obj (M.obj B))
  | .body b => denote J M b

noncomputable def blockArrow (arrows : LabelArrows J M L T) :
    Block Φ L A → (J.obj (M.obj A) ⟶ T)
  | .jump op join => call J M op ≫ arrows _ join
  | .branch op left right => choice J M op ≫ coprod.desc (arrows _ left) (arrows _ right)

/-- A solution gives each allocated block the continuation determined by
its outgoing edges. Old labels are parameters of this system. -/
def Solves : {R : List τ} → Extension Φ L R → LabelArrows J M R T → Prop
  | _, .empty, _ => True
  | _, .push (A := A) prev block, arrows =>
    let next := fun X p => arrows X (shiftSite A p)
    arrows A (headSite A _) = blockArrow J M next block ∧ Solves prev next

noncomputable def blockArrows (p : Compiled Φ L A) :
    ∀ i, J.obj (M.obj (p.localTypes i)) ⟶ J.obj (labelObj M (List.ofFn p.localTypes ++ L)) :=
  fun i => blockArrow J M (fun _ s => J.map (siteArrow M s)) (p.blockAt i)

/-- The step is the same finite-label dispatcher used by LambdaSSA's CFG
denotation. Acyclicity will make its Elgot fixpoint a finite fold. -/
noncomputable def cfgStep (p : Compiled Φ L A) :=
  cfgStepOf J M p.localTypes L (blockArrows J M p)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical
