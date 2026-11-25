module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.LocallySmallValidity.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Defs

/-! # Repaired validity for LetIter with named free variables -/

@[expose] public section

open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasType AbortEquiv)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w r u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

namespace NamedContext

variable {ν : Type w} {τ : Type u} {Φ : Type v}

/-- Copy the types of all free slots into a newest-first bound context. -/
def freeSlots (Γ : Ctx ν τ) : BoundCtx τ Γ.length :=
  match Γ with
  | .nil => .nil
  | .snoc Γ _ A => .snoc (freeSlots Γ) A

/-- Find the newest slot selected by a free name. -/
def lookupSlot [DecidableEq ν] (x : ν) (Γ : Ctx ν τ) : Option (Fin Γ.length) :=
  match Γ with
  | .nil => none
  | .snoc Γ name _ =>
    match name with
    | none => (lookupSlot x Γ).map Fin.succ
    | some y => if x = y then some (0 : Fin (Γ.length + 1)) else (lookupSlot x Γ).map Fin.succ

/-- Place the added slots behind all of the original bound indices. -/
def prepend {k : Nat} (α : BoundCtx τ k) : {n : Nat} → BoundCtx τ n → BoundCtx τ (k + n)
  | _, .nil => α
  | _, .snoc β A => .snoc (prepend α β) A

def freeIndex {k : Nat} (i : Fin k) : (n : Nat) → Fin (k + n)
  | 0 => i
  | n + 1 => (freeIndex i n).succ

def boundIndex (k : Nat) : {n : Nat} → Fin n → Fin (k + n)
  | 0, i => i.elim0
  | _ + 1, i => Fin.cases 0 (fun j => (boundIndex k j).succ) i

/-- Replace each visible name by its shifted slot index. Unbound names
are outside the typed domain of this translation. -/
def closeTm [DecidableEq ν] (Γ : Ctx ν τ) :
    {n : Nat} → Tm ν Φ n → Tm Empty Φ (Γ.length + n)
  | n, .fv x => match lookupSlot x Γ with
    | none => .unit
    | some i => .bv (freeIndex i n)
  | _, .bv i => .bv (boundIndex Γ.length i)
  | _, .op f a => .op f (closeTm Γ a)
  | _, .let₁ a b => .let₁ (closeTm Γ a) (closeTm Γ b)
  | _, .unit => .unit
  | _, .pair a b => .pair (closeTm Γ a) (closeTm Γ b)
  | _, .let₂ a b => .let₂ (closeTm Γ a) (closeTm Γ b)
  | _, .inl a => .inl (closeTm Γ a)
  | _, .inr a => .inr (closeTm Γ a)
  | _, .case e l r => .case (closeTm Γ e) (closeTm Γ l) (closeTm Γ r)
  | _, .abort a => .abort (closeTm Γ a)
  | _, .iter a b => .iter (closeTm Γ a) (closeTm Γ b)

section Environment

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [TypeFormers τ] (M : TypeModel τ V)

theorem freeSlots_obj (Γ : Ctx ν τ) : ctxObj M Γ = boundObj M (freeSlots Γ) := by
  induction Γ with
  | nil => rfl
  | snoc Γ x A ih => exact congrArg (fun R => R ⊗ M.obj A) ih

def closeEnvIso (Γ : Ctx ν τ) :
    {n : Nat} → (β : BoundCtx τ n) →
      envObj M Γ β ≅ envObj M (Ctx.nil : Ctx Empty τ) (prepend (freeSlots Γ) β)
  | _, .nil => (ρ_ _).trans ((eqToIso (freeSlots_obj M Γ)).trans ((λ_ _).symm))
  | _, .snoc β A => (envSnocIso M Γ β A).symm ≪≫
      MonoidalCategory.whiskerRightIso (closeEnvIso Γ β) (M.obj A) ≪≫
      envSnocIso M (Ctx.nil : Ctx Empty τ) (prepend (freeSlots Γ) β) A

end Environment

/-- Every retained environment slot has a visible name. -/
def AllSlotsVisible [DecidableEq ν] (Γ : Ctx ν τ) : Prop :=
  ∀ i : Fin Γ.length, ∃ x, lookupSlot x Γ = some i

/-- Name an indexed newest-first context by insertion position. Legacy contexts
of annotated types can use this construction after projecting their types. -/
def nameIndexedSlots : List τ → Ctx Nat τ
  | [] => .nil
  | A :: rest => .snoc (nameIndexedSlots rest) (some rest.length) A

end NamedContext

variable {ν : Type w} [DecidableEq ν]
  {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  {Γ : Ctx ν τ} (pe : ε)

/-- Equality in the split-universe repaired model class, with full typing
coherence over the given name type. -/
def RepairedNamedLocallySmallValidity
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) : Prop :=
  ∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C)
    [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel τ V) [InstructionModel J M Φ],
    TypingCoherent (ν := ν) J M Φ →
    (∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) R S = eqToIso e) →
    (∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p) →
    denote J M da = denote J M db

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
