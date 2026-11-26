module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.FiniteExitInstitution

/-! # A native finite-exit institution and its exact LetCase comparison -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Corridor Room Inst)
open Morphism (SignatureMap)
open LambdaSSA.Acyclic (FiniteExit)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ) [h.PreservesProducts] [h.PreservesSums]

@[simp] theorem mapFiniteExit_id (e : FiniteExitEquation P) :
    mapFiniteExit (P := P) (Q := P) SignatureMap.id e = e :=
  mapFiniteExit_id_proof e

theorem mapFiniteExit_comp (e : FiniteExitEquation P) :
    mapFiniteExit (h.comp g) e = mapFiniteExit h (mapFiniteExit g e) :=
  mapFiniteExit_comp_proof g h e

/-- Packing is natural for the existing exact SSA equation map. -/
theorem encodeFiniteExit_map (e : FiniteExitEquation P) :
    encodeFiniteExit (mapFiniteExit g e) = mapSSASignature g (encodeFiniteExit e) :=
  encodeFiniteExit_map_proof g e

/-- Compilation is natural for the existing exact LetCase equation map. -/
theorem compileFiniteExit_map (e : FiniteExitEquation P) :
    compileFiniteExit (mapFiniteExit g e) = mapCaseSignature g (compileFiniteExit e) :=
  (congrArg compile (encodeFiniteExit_map g e)).trans (compile_mapSSASignature g (encodeFiniteExit e))

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

/-- Forward transport identifies the native arrows after mapping the
ordered exits and the positional context. -/
theorem denoteFiniteExit_pullback (K : CoherentRegionModel J Q)
    {n : Nat} {β : BoundCtx τ n} {L : List τ} (c : FiniteExit P.Instr L β) :
    HEq ((K.pullbackOfWitness g (regionWitnessPullback g K)).denoteFiniteExit J c)
      (K.denoteFiniteExit J (c.mapSignature g)) :=
  denoteFiniteExit_pullback_proof g K c

variable [FreydCategory.CentralUnit J]

/-- Packing preserves and reflects equality of native arrows in the same model. -/
theorem sat_encodeFiniteExit (K : (ssaRoom J P).Mod) (e : FiniteExitEquation P) :
    (ssaRoom J P).Sat K (encodeFiniteExit e) ↔ (finiteExitRoom J P).Sat K e :=
  sat_encodeFiniteExit_proof K e

/-- The native room uses the same signature reduct as the exact SSA room. -/
noncomputable def finiteExitCorridor : finiteExitRoom J P ⟶ finiteExitRoom J Q where
  sen := mapFiniteExit g
  mod := (ssaSignatureCorridor g).mod
  sat K e :=
    let l := denoteFiniteExit_pullback g K.fromShrinkHoms.as e.2.1
    let r := denoteFiniteExit_pullback g K.fromShrinkHoms.as e.2.2
    ⟨fun eq => eq_of_heq (l.trans ((heq_of_eq eq).trans r.symm)),
      fun eq => eq_of_heq (l.symm.trans ((heq_of_eq eq).trans r))⟩

/-- Packing is a corridor with the identity model functor. -/
noncomputable def encodeFiniteExitCorridor (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) : finiteExitRoom J P ⟶ ssaRoom J P :=
  ⟨encodeFiniteExit, 𝟭 _, sat_encodeFiniteExit⟩

/-- Compilation to validated LetCase compares satisfaction in the actual
native room with satisfaction in the recovered model's algebra. -/
noncomputable def compileFiniteExitCorridor (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) : finiteExitRoom J P ⟶ validatedRoom J P :=
  encodeFiniteExitCorridor J P ≫ validatedCompileCorridor J P

/-- At a validated algebra, the compiled sentence holds exactly when the
expanded model satisfies the original positional equation. -/
theorem sat_compileFiniteExit (A : (validatedRoom J P).Mod) (e : FiniteExitEquation P) :
    (validatedRoom J P).Sat A (compileFiniteExit e) ↔
      (finiteExitRoom J P).Sat ((validatedCompileCorridor J P).mod.obj A) e :=
  (compileFiniteExitCorridor J P).sat A e

/-- The model categories and their reductions are the existing discrete
coherent ones. Sentences use the native finite interfaces. -/
noncomputable def finiteExitInst (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : TypeSignature ⥤ Room.{0, 0, 1} where
  obj P := finiteExitRoom J P.prim
  map f := finiteExitCorridor f.signatureMap
  map_id P := Room.hom_ext (funext mapFiniteExit_id)
    (congrArg (fun c : ssaRoom J P.prim ⟶ ssaRoom J P.prim => c.mod) ssaSignatureCorridor_id)
  map_comp {P _ S} f g := Room.hom_ext (funext (mapFiniteExit_comp f.signatureMap g.signatureMap))
    (congrArg (fun c : ssaRoom J P.prim ⟶ ssaRoom J S.prim => c.mod)
      (ssaSignatureCorridor_comp f.signatureMap g.signatureMap))

/-- Packing is natural as a square of full corridors. -/
noncomputable def encodeFiniteExitNatural (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : finiteExitInst J ⟶ ssaTypeInst J where
  app P := encodeFiniteExitCorridor J P.prim
  naturality {_ _} f := Room.hom_ext (funext (encodeFiniteExit_map f.signatureMap)) rfl

/-- The finite-exit comparison to exact LetCase is natural over type-changing signatures. -/
noncomputable def compileFiniteExitNatural (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : finiteExitInst J ⟶ validatedTypeInst J :=
  encodeFiniteExitNatural J ≫ validatedCompileNatural J

/-- The native finite-exit institution uses the existing type-changing signatures. -/
noncomputable def finiteExitInstitution (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : Inst.{1, 0, 0, 0, 1} :=
  ⟨TypeSignature, finiteExitInst J⟩

/-- The exact LetCase comparison as an institution comorphism. -/
noncomputable def compileFiniteExitComorphism (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] :
    Inst.CoHom (finiteExitInstitution J) (validatedCaseInstitution J) where
  Φ := 𝟭 TypeSignature
  ρ := compileFiniteExitNatural J ≫ (Functor.leftUnitor (validatedTypeInst J)).inv

end Silmaril.Isotope.Institution.Acyclic
