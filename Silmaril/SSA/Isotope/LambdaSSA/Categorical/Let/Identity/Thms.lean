module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Let.Identity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.IdentityLet

/-! # Categorical validity of identity lets

The retained-input bind followed by the newest-variable projection returns
the originally computed result. Naturality of that projection along a
computation uses centrality of the Freyd unit comparison. When the scrutinee
already denotes a value map, the Cartesian pairing equation suffices.
-/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Proofs.SSA.Isotope.LambdaSSA

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

local notation "U" => Functor.StrongPremonoidal.unitIso (J := J)

variable {Γ : VCtx τ} {s t : Tm Φ} {A : τ} {hs : Tm.HasType Γ s A} {ht : Tm.HasType Γ t A}

/-- The newest-variable let continuation preserves the scrutinee's structural
arrow with a central unit comparison, including for effectful scrutinees. -/
theorem Denotes.let₁_identity (hu : IsCentral (U).hom)
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} (d : Denotes J M ht f) :
    Denotes J M (.let₁ ht (.var (i := 0) rfl)) f :=
  IdentityLet.term J M hu d

/-- A value-map scrutinee satisfies the identity law by Cartesian projection. -/
theorem Denotes.let₁_identity_of_map {p : ctxObj M Γ ⟶ M.obj A}
    (d : Denotes J M ht (J.map p)) : Denotes J M (.let₁ ht (.var (i := 0) rfl)) (J.map p) :=
  IdentityLet.termOfMap J M d

/-- The left operand can use the value-map identity-let rule even when the
right operand is effectful. Both pairs share the same sequential arrow. -/
theorem pair_identityLet_denotes_of_map {B : τ} {b : Tm Φ} {hb : Tm.HasType Γ b B}
    {p : ctxObj M Γ ⟶ M.obj A} {g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj B)}
    (dt : Denotes J M ht (J.map p)) (db : Denotes J M hb g) :
    ∃ f, Denotes J M (.pair (.let₁ ht (.var (i := 0) rfl)) hb) f ∧
      Denotes J M (.pair ht hb) f :=
  ⟨_, .pair (dt.let₁_identity_of_map J M) db, .pair dt db⟩

/-- Typed expression contexts preserve the shared denotation of an identity-let
contraction. The two typings have the same external context and result type. -/
theorem identityLet_denotes (hu : IsCentral (U).hom) (h : Tm.IdentityLet hs ht) :
    ∃ f, Denotes J M hs f ∧ Denotes J M ht f :=
  IdentityLet.inContext J M hu h

/-- Typing coherence turns the common graph arrow into an equality of the
chosen denotations. -/
theorem denote_eq_of_identityLet [TypingCoherent (Φ := Φ) J M] (hu : IsCentral (U).hom)
    (h : Tm.IdentityLet hs ht) : denote J M hs = denote J M ht := by
  obtain ⟨_, ds, dt⟩ := identityLet_denotes J M hu h
  exact (ds.eq_denote J M).symm.trans (dt.eq_denote J M)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
