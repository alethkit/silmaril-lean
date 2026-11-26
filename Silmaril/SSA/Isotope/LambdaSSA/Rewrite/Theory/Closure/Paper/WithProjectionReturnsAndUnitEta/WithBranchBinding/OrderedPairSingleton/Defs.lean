module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.ReturnSeeds.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms

/-! # Raw singleton representatives for the ordered-pair join -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton

open CategoryTheory
open Paper.Extension.Singleton (ofType ofRegion ofRegion_eq_iff)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "G" => ofType (Φ := Φ) Seed

variable {A B C : τ}

/-- A raw representative has exact singleton typing. -/
abbrev Rep (A B : τ) := {r : Region Φ // HasType [A] r [B]}

def rawSetoid (A B : τ) : Setoid (Rep (Φ := Φ) A B) where
  r r s := Extension.Eqv (AddBinding Seed) [A] r.val s.val [B]
  iseqv := ⟨fun r => Extension.Eqv.refl r.property, Extension.Eqv.symm, Extension.Eqv.trans⟩

/-- The raw singleton hom quotient uses the ordered-pair join with the branch rule. -/
abbrev RawHom (A B : τ) := Quotient (rawSetoid (Φ := Φ) pe A B)

def rawClass {r : Region Φ} (hr : HasType [A] r [B]) : RawHom (Φ := Φ) pe A B :=
  Quotient.mk _ ⟨r, hr⟩

/-- Interpret a raw arrow in the existing guarded singleton quotient. -/
def normalizeHom (f : RawHom (Φ := Φ) pe A B) : G A ⟶ G B :=
  Quotient.liftOn f (fun r => ofRegion Seed r.property.bindBranchArguments)
    (fun r s e => (ofRegion_eq_iff Seed r.property.bindBranchArguments s.property.bindBranchArguments).mpr
      (eqv_normalize_of_guardedSeed pairJoined_valueBranches e))

theorem singletonContinuation_typed {r : Region Φ} (hr : HasType [A] r [B]) :
    LSubst.HasType [] [A] [B] (fun _ => r) :=
  fun _ _ h => (List.mem_singleton.mp (List.mem_of_getElem? h)).symm ▸ hr

def composeRep (r : Rep (Φ := Φ) A B) (s : Rep (Φ := Φ) B C) : Rep (Φ := Φ) A C :=
  ⟨compLSubst (fun _ => r.val.bindBranchArguments) (fun _ => s.val) 0,
    r.property.bindBranchArguments.hasType.lsubst ((singletonContinuation_typed s.property).liftVars A)⟩

/-- Identity is the literal identity branch. -/
def identity (A : τ) : RawHom (Φ := Φ) pe A A :=
  rawClass pe (.br (ℓ := 0) rfl (.var (i := 0) rfl))

/-- Objects of the raw singleton category are syntax types. -/
structure RawTypeCategory (Φ : Type v) (pe : ε) where
  as : τ

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton
