module

public import Silmaril.Semantics.RuntimeWires.Polygraph.Defs

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs

open CategoryTheory

universe u v

theorem emptyHom_ext {O P : Type u} {T : Signature.{u,v} P} {f : O → P}
    (a b : Signature.Hom (Signature.empty O) T f) : a = b := by
  have h : a.edge = b.edge := funext fun e => e.elim
  cases a
  cases b
  cases h
  rfl

def lift {G : Polygraph.{u,v}} {H : EffectfulPolygraph.{u,v}}
    (f : G ⟶ EffectfulPolygraph.forgetPure.obj H) :
    G.allEffectful ⟶ H :=
  EffectfulPolygraph.Hom.mk f.obj (Signature.Hom.ofEmpty H.pure f.obj) f.edges

theorem lift_comp {G H : Polygraph.{u,v}} {K : EffectfulPolygraph.{u,v}}
    (f : G ⟶ H) (g : H ⟶ EffectfulPolygraph.forgetPure.obj K) :
    lift (f ≫ g) = lift (H := H.allEffectful) f ≫ lift g :=
  congrArg (fun p => EffectfulPolygraph.Hom.mk (G := G.allEffectful) (H := K)
    (g.obj ∘ f.obj) p (f.edges.comp g.edges)) (emptyHom_ext _ _)

def allEffectful : Polygraph.{u,v} ⥤ EffectfulPolygraph.{u,v} where
  obj := Polygraph.allEffectful
  map {G H} f := lift (G := G) (H := H.allEffectful) f
  map_id G :=
    congrArg (fun p => EffectfulPolygraph.Hom.mk (G := G.allEffectful) (H := G.allEffectful)
      id p (Signature.Hom.id G.edges)) (emptyHom_ext _ _)
  map_comp {G H K} f g := lift_comp (G := G) (H := H) (K := K.allEffectful) f g

def allEffectfulAdjunction : allEffectful.{u,v} ⊣ EffectfulPolygraph.forgetPure :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G H =>
        { toFun := fun f => Polygraph.Hom.mk f.obj f.effect
          invFun := lift (G := G) (H := H)
          left_inv := fun f => by
            change EffectfulPolygraph.Hom G.allEffectful H at f
            cases f with
            | mk obj pure effect =>
              exact congrArg (fun p => EffectfulPolygraph.Hom.mk (G := G.allEffectful)
                (H := H) obj p effect) (emptyHom_ext _ _)
          right_inv := fun _ => rfl }
      homEquiv_naturality_left_symm := fun f g => lift_comp f g
      homEquiv_naturality_right := fun _ _ => rfl }

end Silmaril.RuntimeWires.Proofs
