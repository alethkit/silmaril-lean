module

public import Silmaril.Semantics.Calco2019.Defs
public import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Final coalgebras of parametrized monads (CALCO 2019, Article 13, §5)

Proposition 23 uses the monad structure in the result argument and functoriality
in the parameter. Its coalgebra constructions apply without guarded iteration.
-/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

variable {C : Type u} [Category.{v} C]

/-- The monad-valued functor underlying a parametrized guarded Elgot monad. -/
abbrev ParametrizedMonad (C : Type u) [Category.{v} C] := C ⥤ CategoryTheory.Monad C

namespace ParametrizedMonad

variable (M : ParametrizedMonad C)

/-- Freeze the result object and act functorially in the parameter. -/
abbrev parameter (X : C) : C ⥤ C where
  obj W := (M.obj W).obj X
  map g := (M.map g).app X
  map_id W := by rw [M.map_id]; rfl
  map_comp g h := by rw [M.map_comp]; rfl

/-- Kleisli extension at a fixed parameter. -/
def extend {W X Y : C} (f : X ⟶ (M.obj W).obj Y) :
    (M.obj W).obj X ⟶ (M.obj W).obj Y :=
  (M.obj W).map f ≫ (M.obj W).μ.app Y

end ParametrizedMonad

/-- The existence assumption of Proposition 23, with a chosen final coalgebra at each result
object. -/
structure FinalResumptions (M : ParametrizedMonad C) where
  coalgebra (X : C) : Coalgebra (M.parameter X)
  final (X : C) : IsTerminal (coalgebra X)

namespace FinalResumptions

variable {M : ParametrizedMonad C} (R : FinalResumptions M)

abbrev obj (X : C) : C := (R.coalgebra X).V
abbrev out (X : C) : R.obj X ⟶ (M.obj (R.obj X)).obj X := (R.coalgebra X).str

/-- The canonical map from any coalgebra to the final one. -/
def unfold {X S : C} (body : S ⟶ (M.obj S).obj X) : S ⟶ R.obj X :=
  (R.final X).from (⟨S, body⟩ : Coalgebra (M.parameter X)) |>.f

/-- Inverse to the final-coalgebra observation map, by Lambek's lemma. -/
def roll (X : C) : (M.obj (R.obj X)).obj X ⟶ R.obj X :=
  Coalgebra.Terminal.strInv (R.final X)

/-- The resumption unit, given by a single observation returning immediately. -/
def unit (X : C) : X ⟶ R.obj X :=
  (M.obj (R.obj X)).η.app X ≫ R.roll X

/-- The diagram of Proposition 23(1). -/
def IsExtension {X Y : C} (f : X ⟶ R.obj Y) (k : R.obj X ⟶ R.obj Y) : Prop :=
  k ≫ R.out Y = R.out X ≫ (M.parameter X).map k ≫ M.extend (f ≫ R.out Y)

variable (P : Coproducts C)

/-- The coproduct coalgebra used to extend a Kleisli map by finality. -/
def extensionBody {X Y : C} (f : X ⟶ R.obj Y) :
    P.sum (R.obj X) (R.obj Y) ⟶ (M.obj (P.sum (R.obj X) (R.obj Y))).obj Y :=
  P.desc
    (R.out X ≫ (M.parameter X).map P.inl ≫
      M.extend (W := P.sum (R.obj X) (R.obj Y))
        (f ≫ R.out Y ≫ (M.parameter Y).map P.inr))
    (R.out Y ≫ (M.parameter Y).map P.inr)

/-- The Kleisli extension of a resumption map, obtained by finality. -/
def extend {X Y : C} (f : X ⟶ R.obj Y) : R.obj X ⟶ R.obj Y :=
  P.inl ≫ R.unfold (R.extensionBody P f)

/-- The diagram of Proposition 23(2). -/
def IsSolution {X Y : C} (f : X ⟶ (M.obj (R.obj (P.sum Y X))).obj Y)
    (g : X ⟶ R.obj Y) : Prop :=
  g ≫ R.out Y = f ≫ (M.parameter Y).map (R.extend P (P.desc (R.unit Y) g))

/-- Eliminate one immediate return or recursive call to get a coalgebra with result `Y`. -/
def solutionBody {X Y : C} (f : X ⟶ (M.obj (R.obj (P.sum Y X))).obj Y) :
    R.obj (P.sum Y X) ⟶ (M.obj (R.obj (P.sum Y X))).obj Y :=
  R.out (P.sum Y X) ≫
    M.extend (W := R.obj (P.sum Y X)) (P.desc ((M.obj (R.obj (P.sum Y X))).η.app Y) f)

/-- The solution of the recursive diagram in Proposition 23(2). -/
def solve {X Y : C} (f : X ⟶ (M.obj (R.obj (P.sum Y X))).obj Y) : X ⟶ R.obj Y :=
  f ≫ (M.parameter Y).map (R.unfold (R.solutionBody P f)) ≫ R.roll Y

end FinalResumptions

end Silmaril.Calco2019
