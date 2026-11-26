module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Resumption.Thms

/-! # Shape-respecting observations over free SSA types -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape

open Resumption.Typing (InstrTyped)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)]

export Resumption.Typing (ValueTyped EnvTyped)

/-- The existing observation model over an exactly typed environment.
Atomic typing may depend on the base type. A successful primitive must
produce a target-typed reply whenever its input has the source type.
The fault and divergence relations carry no reply value. -/
structure Model (Φ : Type u) {κ : Type v} [HasTy Φ (Ty κ)] (Γ : VCtx (Ty κ)) where
  raw : Institution.Observational.Model.{u,w,x} Φ Γ.length
  atomType : raw.α → κ → Prop
  boundTyped : ∀ i : Fin Γ.length, ValueTyped atomType (raw.bound i) (Γ.get i)
  instrTyped : InstrTyped atomType raw.instr

/-- Bind an ordinary exit payload at its declared label type. -/
abbrev Model.extend {Γ : List (Ty κ)} (M : Model.{u,v,w,x} Φ Γ) {A : Ty κ}
    {a : Value M.raw.α} (typed : ValueTyped M.atomType a A) : Model.{u,v,w,x} Φ (A :: Γ) where
  raw := extendModel M.raw a
  atomType := M.atomType
  boundTyped i := Fin.cases typed (fun j => M.boundTyped j) i
  instrTyped := M.instrTyped

/-- Evaluate in the same observational relations and the same fresh-top order. -/
noncomputable def denote {Γ L : List (Ty κ)} (r : Region Φ Γ L)
    (M : Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) : Behaviour L.length M.raw.α M.raw.σ :=
  Overlay.denote r M.raw s

/-- Only an ordinary exit carries a payload. Fresh UB has no typed return,
even though projecting it to a set yields every positional outcome. -/
def ReturnsTyped {α : Type w} {σ : Type x} (atomType : α → κ → Prop) {L : List (Ty κ)}
    (p : Behaviour L.length α σ) : Prop :=
  ∀ ⦃i a s⦄, p.Ordinary (.ret i a s) → ValueTyped atomType a (L.get i)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape
