module

public import Silmaril.Semantics.Calco2019.Thms
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # The dual finite-automaton identities mentioned in Remark 15 -/

@[expose] public section

universe u v u' v' w w'

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory CategoryTheory.Limits

variable {C : Type u'} [Category.{v'} C] {K : Type u} [Category.{v} K]
  {P : Coproducts K} {X : C} {I : Type w} {L : Type w'} (J : C ⥤ K)

/-- The cofan obtained by embedding each state injection into the category of computations. -/
def imageCofan (c : Cofan (fun _ : I => X)) : Cofan (fun _ : I => J.obj X) :=
  Cofan.mk (J.obj c.pt) (fun i => J.map (c.inj i))

variable {c : Cofan (fun _ : I => X)} {a : Cofan (fun _ : L => X)}

/-- The structural map which identifies all copies of a state object. -/
def foldStates (hc : IsColimit c) : c.pt ⟶ X :=
  Cofan.IsColimit.desc hc (fun _ => 𝟙 X)

/-- The structural map that sends the copy for a letter to the copy for its successor state. -/
def selectStates (ha : IsColimit a) (step : I → L → I) (i : I) : a.pt ⟶ c.pt :=
  Cofan.IsColimit.desc ha (fun l => c.inj (step i l))

/-- Run the same body at each state with the recursive outputs sent to their successors. -/
def automatonBody {Y : K} (hc : IsColimit (imageCofan J c)) (ha : IsColimit a)
    (step : I → L → I) (body : J.obj X ⟶ P.sum Y (J.obj a.pt)) :
    J.obj c.pt ⟶ P.sum Y (J.obj c.pt) :=
  Cofan.IsColimit.desc hc (fun i => body ≫ P.map (𝟙 Y) (J.map (selectStates ha step i)))

/-- The coproduct map induced by reindexing copies of the same object. -/
def stateReindex (hc : IsColimit c) (p : I → L) : c.pt ⟶ a.pt :=
  Cofan.IsColimit.desc hc (fun i => a.inj (p i))

/-- The large system in the commutative identity. The equation at state
`i` first runs the equation selected by `p i`, then reindexes its recursive
outputs by `route i`. -/
def commutativeBody {Y : K} (hc : IsColimit c) (hk : IsColimit (imageCofan J c))
    (p : I → L) (route : I → I → I) (body : J.obj a.pt ⟶ P.sum Y (J.obj c.pt)) :
    J.obj c.pt ⟶ P.sum Y (J.obj c.pt) :=
  Cofan.IsColimit.desc hk (fun i =>
    J.map (a.inj (p i)) ≫ body ≫ P.map (𝟙 Y) (J.map (stateReindex hc (a := c) (route i))))

end Silmaril.Calco2019.Guardedness
