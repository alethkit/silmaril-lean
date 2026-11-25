module

public import Silmaril.Semantics.Calco2019.Trace.Automata.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Automata

/-! # Uniformity implies the dual automaton identities -/

public section

universe u v u' v' w w'

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory CategoryTheory.Limits

variable {C : Type u'} [Category.{v'} C] {K : Type u} [Category.{v} K]
  {P : Coproducts K} {G : Guardedness P} {X : C} {I : Type w} {L : Type w'} {J : C ⥤ K}
  {c : Cofan (fun _ : I => X)} {a : Cofan (fun _ : L => X)}

/-- The coproduct dual of Ésik's automaton identity, Definition 2.3 of
*Equational axioms associated with finite automata for fixed point operations
in cartesian categories*. Uniformity with respect to the structural fold
gives the equation, including the finite total case of Remark 15. -/
theorem automatonIdentity (F : G.Fixpoints) (uniform : F.Uniform J)
    (hc : IsColimit c) (hk : IsColimit (imageCofan J c)) (ha : IsColimit a)
    {Y : K} (step : I → L → I) (body : J.obj X ⟶ P.sum Y (J.obj a.pt))
    (single : G.guarded (body ≫ P.map (𝟙 Y) (J.map (foldStates ha))))
    (multi : G.guarded (automatonBody J hk ha step body)) :
    F.iterate (automatonBody J hk ha step body) multi =
      J.map (foldStates hc) ≫ F.iterate (body ≫ P.map (𝟙 Y) (J.map (foldStates ha))) single :=
  Proofs.Feedback.automatonIdentity hc hk ha F uniform step body single multi

/-- The commutative identity with a base reindexing `p` and state maps
within its fibers. The proof needs only that each `route i` preserves the
fibers, so it includes the traditional surjective finite reindexing. -/
theorem commutativeIdentity (F : G.Fixpoints) (uniform : F.Uniform J)
    (hc : IsColimit c) (hk : IsColimit (imageCofan J c))
    {Y : K} (p : I → L) (route : I → I → I) (fibers : ∀ i j, p (route i j) = p j)
    (body : J.obj a.pt ⟶ P.sum Y (J.obj c.pt))
    (small : G.guarded (body ≫ P.map (𝟙 Y) (J.map (stateReindex hc p))))
    (large : G.guarded (commutativeBody J hc hk p route body)) :
    F.iterate (commutativeBody J hc hk p route body) large =
      J.map (stateReindex hc p) ≫ F.iterate (body ≫ P.map (𝟙 Y) (J.map (stateReindex hc p))) small :=
  Proofs.Feedback.commutativeIdentity hc hk F uniform p route fibers body small large

end Silmaril.Calco2019.Guardedness
