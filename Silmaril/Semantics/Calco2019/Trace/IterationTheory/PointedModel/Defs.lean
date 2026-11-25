module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Commutative.Defs
public import Silmaril.Semantics.Calco2019.OmegaContinuous.Thms
public import Silmaril.Semantics.Domain.Function

/-! # The coproduct dual of the pointed ω-cpo model -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.IterationTheory.PointedModel

open CategoryTheory CategoryTheory.Limits
open OmegaCompletePartialOrder Silmaril.Semantics.Domain

/-- A pointed domain, used in the opposite of the continuous-map category. -/
structure Object where
  domain : Silmaril.DomainCat.{u}

instance : CoeSort Object.{u} (Type u) := ⟨fun X => X.domain.carrier⟩

instance (X : Object) : OmegaCompletePartialOrder X := X.domain.cpo
instance (X : Object) : OrderBot X := X.domain.bot

/-- Bundle a pointed ω-cpo in the opposite continuous-map category. -/
abbrev of (D : Type u) [OmegaCompletePartialOrder D] [OrderBot D] : Object.{u} :=
  ⟨Silmaril.DomainCat.of D⟩

instance : Category.{u} Object.{u} where
  Hom X Y := Y →𝒄 X
  id _ := ContinuousHom.id
  comp f g := f.comp g
  id_comp _ := ContinuousHom.ext _ _ fun _ => rfl
  comp_id _ := ContinuousHom.ext _ _ fun _ => rfl
  assoc _ _ _ := ContinuousHom.ext _ _ fun _ => rfl

noncomputable instance (X Y : Object) : OmegaCompletePartialOrder (X ⟶ Y) :=
  inferInstanceAs (OmegaCompletePartialOrder (Y →𝒄 X))

instance (X Y : Object) : OrderBot (X ⟶ Y) :=
  inferInstanceAs (OrderBot (Y →𝒄 X))

/-- The continuous map underlying a morphism, with the direction reversed. -/
abbrev run {X Y : Object} (f : X ⟶ Y) : Y →𝒄 X := f

/-- In the opposite category a binary product of domains is a coproduct. -/
def coproducts : Coproducts Object.{u} where
  sum X Y := of (X × Y)
  inl := fstHom
  inr := sndHom
  isColimit X Y := BinaryCofan.isColimitMk (fun c => pairHom c.inl c.inr)
    (fun _ => ContinuousHom.ext _ _ fun _ => rfl)
    (fun _ => ContinuousHom.ext _ _ fun _ => rfl)
    (fun _ _ hl hr => ContinuousHom.ext _ _ fun z =>
      Prod.ext (congrArg (fun f : _ →𝒄 X => f z) hl)
        (congrArg (fun f : _ →𝒄 Y => f z) hr))

/-- In the opposite category a power of one domain is its copower. -/
def copowers (X : Object.{u}) : FiniteCopowers X where
  cofan I := Cofan.mk (of (I → X)) evalHom
  colimit _ := Cofan.IsColimit.mk _
    (fun c => piHom fun i => run (c.inj i))
    (fun _ _ => ContinuousHom.ext _ _ fun _ => rfl)
    (fun c _ h => ContinuousHom.ext _ _ fun y => funext fun i =>
      congrArg (fun k : X ⟶ c.pt => run k y) (h i))

/-- A node emits its label at the root and follows the given child at an
in-range argument index. -/
noncomputable def pathOperation {σ : Signature.{u}} {E : Type v} (a : σ.Symbol) :
    (Fin (σ.arity a) → PathDomain σ E) →𝒄 PathDomain σ E :=
  piHom fun
    | [] => ContinuousHom.const (Part.some (.inl a))
    | i :: path => if h : i < σ.arity a then
        (evalHom (P := fun _ : List Nat => Part (σ.Symbol ⊕ E)) path).comp
          (evalHom (P := fun _ : Fin (σ.arity a) => PathDomain σ E) ⟨i, h⟩)
      else ContinuousHom.const ⊥

/-- Interpret the signature on partial path observations, with one domain
coordinate for each parameter. -/
noncomputable def pathInterpretation (σ : Signature.{u}) (E : Type) [Finite E] :
    Interpretation (copowers (of (PathDomain σ E))) σ E (of (E → PathDomain σ E)) where
  op := pathOperation
  exit := evalHom
  bottom := ⊥

/-- Assign each parameter a distinct root observation. -/
def markedParameters (σ : Signature.{u}) (E : Type v) : E → PathDomain σ E :=
  fun e path => match path with
    | [] => Part.some (.inr e)
    | _ :: _ => ⊥

end Silmaril.Calco2019.IterationTheory.PointedModel
