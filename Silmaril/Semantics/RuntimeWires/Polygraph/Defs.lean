module

public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

/-!
# Polygraphs for effectful string diagrams

Definitions 3.1 and 3.7 of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories* (LMCS 21(2), 2025),
<https://doi.org/10.46298/LMCS-21(2:9)2025>.
-/

namespace Silmaril.RuntimeWires

open CategoryTheory

universe u v

/-- Generators over an object type, with ordered input and output boundaries. The fiber
over a pair of lists is the generator family used in the paper. -/
structure Signature (Obj : Type u) where
  Edge : Type v
  source : Edge → List Obj
  target : Edge → List Obj

namespace Signature

/-- A generator map covering a fixed object map. -/
structure Hom {O P : Type u} (S : Signature.{u,v} O) (T : Signature.{u,v} P)
    (f : O → P) where
  edge : S.Edge → T.Edge
  source (e : S.Edge) : T.source (edge e) = (S.source e).map f
  target (e : S.Edge) : T.target (edge e) = (S.target e).map f

/-- The signature without generators on the given objects. -/
def empty (O : Type u) : Signature.{u,v} O where
  Edge := PEmpty
  source := PEmpty.elim
  target := PEmpty.elim

/-- Identity generator map. -/
def Hom.id {O : Type u} (S : Signature.{u,v} O) : Hom S S id where
  edge := _root_.id
  source _ := (List.map_id _).symm
  target _ := (List.map_id _).symm

/-- Compose generator maps covering the composite object map. -/
def Hom.comp {O P Q : Type u} {S : Signature.{u,v} O} {T : Signature.{u,v} P}
    {U : Signature.{u,v} Q} {f : O → P} {g : P → Q}
    (a : Hom S T f) (b : Hom T U g) : Hom S U (g ∘ f) where
  edge := b.edge ∘ a.edge
  source e := by rw [Function.comp_apply, b.source, a.source, List.map_map]
  target e := by rw [Function.comp_apply, b.target, a.target, List.map_map]

/-- The unique map out of the empty signature over a given object map. -/
def Hom.ofEmpty {O P : Type u} (T : Signature.{u,v} P) (f : O → P) :
    Hom (empty O) T f where
  edge := PEmpty.elim
  source e := e.elim
  target e := e.elim

end Signature

/-- A polygraph as in Definition 3.1. -/
structure Polygraph where
  Obj : Type u
  edges : Signature.{u,v} Obj

/-- A pair of signatures with the same objects, as in Definition 3.7. -/
structure EffectfulPolygraph where
  Obj : Type u
  pure : Signature.{u,v} Obj
  effect : Signature.{u,v} Obj

namespace Polygraph

/-- A polygraph morphism maps objects and generators, respecting both boundaries. -/
structure Hom (G H : Polygraph.{u,v}) where
  obj : G.Obj → H.Obj
  edges : Signature.Hom G.edges H.edges obj

instance : Category Polygraph.{u,v} where
  Hom := Hom
  id G := ⟨id, Signature.Hom.id G.edges⟩
  comp f g := ⟨g.obj ∘ f.obj, f.edges.comp g.edges⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Interpret every generator as effectful, as in Proposition 5.2. -/
abbrev allEffectful (G : Polygraph.{u,v}) : EffectfulPolygraph.{u,v} :=
  ⟨G.Obj, Signature.empty G.Obj, G.edges⟩

end Polygraph

namespace EffectfulPolygraph

/-- Both generator maps cover the same object map. -/
structure Hom (G H : EffectfulPolygraph.{u,v}) where
  obj : G.Obj → H.Obj
  pure : Signature.Hom G.pure H.pure obj
  effect : Signature.Hom G.effect H.effect obj

instance : Category EffectfulPolygraph.{u,v} where
  Hom := Hom
  id G := ⟨id, Signature.Hom.id G.pure, Signature.Hom.id G.effect⟩
  comp f g := ⟨g.obj ∘ f.obj, f.pure.comp g.pure, f.effect.comp g.effect⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Forget the pure generators, retaining the common objects. -/
def forgetPure : EffectfulPolygraph.{u,v} ⥤ Polygraph.{u,v} where
  obj G := ⟨G.Obj, G.effect⟩
  map f := Polygraph.Hom.mk f.obj f.effect
  map_id _ := rfl
  map_comp _ _ := rfl

end EffectfulPolygraph

end Silmaril.RuntimeWires
