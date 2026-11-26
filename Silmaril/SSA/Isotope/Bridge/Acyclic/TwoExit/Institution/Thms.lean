module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TwoExitInstitution

/-! # Same-model satisfaction for two native exits -/

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LambdaSSA.Acyclic (TwoExit)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

section Signature

variable (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]

/-- Packing commutes with the map on ordinary exact SSA equations. -/
theorem encodeTwoExit_map (e : TwoExitEquation P) :
    encodeTwoExit (mapTwoExit g e) = mapSSASignature g (encodeTwoExit e) :=
  encodeTwoExit_map_proof g e

/-- The compiled equation commutes with the existing exact LetCase map. -/
theorem compileTwoExit_map (e : TwoExitEquation P) :
    compileTwoExit (mapTwoExit g e) = mapCaseSignature g (compileTwoExit e) :=
  (congrArg compile (encodeTwoExit_map g e)).trans (compile_mapSSASignature g (encodeTwoExit e))

/-- Forward witness transport compares the native two-label arrows at
mapped value and exit contexts. -/
theorem denoteTwoExit_pullback (K : CoherentRegionModel J Q) {n : Nat}
    {β : BoundCtx τ n} {A B : τ} (c : TwoExit P.Instr A B β) :
    HEq ((K.pullbackOfWitness g (regionWitnessPullback g K)).denoteTwoExit c)
      (K.denoteTwoExit (c.mapSignature g)) :=
  denoteTwoExit_pullback_proof g K c

/-- Satisfaction of native two-exit equations is invariant under the same
coherent-model reduct as for a single exit. -/
theorem satTwoExit_map (K : CoherentRegionModel J Q) (e : TwoExitEquation P) :
    K.satTwoExit (mapTwoExit g e) ↔
      (K.pullbackOfWitness g (regionWitnessPullback g K)).satTwoExit e := by
  have l := denoteTwoExit_pullback g K e.2.1
  have r := denoteTwoExit_pullback g K e.2.2
  exact ⟨fun h => eq_of_heq (l.trans ((heq_of_eq h).trans r.symm)),
    fun h => eq_of_heq (l.symm.trans ((heq_of_eq h).trans r))⟩

end Signature

variable [FreydCategory.CentralUnit J]

/-- The native denotation of a two-exit computation is preserved by
running its encoded form through the decoder. -/
theorem denoteTwoExit_roundtrip (K : CoherentRegionModel J P) {n : Nat}
    {β : BoundCtx τ n} {A B : τ} (c : TwoExit P.Instr A B β) :
    K.denoteTwoExit (TwoExit.decode c.encode) = K.denoteTwoExit c := by
  let _ := K.instructions
  let _ := K.coherent
  exact TwoExit.denote_decode_encode K.types J c

/-- A native two-exit equation holds exactly when its encoded LetCase
equation holds in the original algebra reduct of the same model. -/
theorem sat_compileTwoExit (K : CoherentRegionModel J P) (e : TwoExitEquation P) :
    ((LetCase.inst (Ctx.nil : Ctx Empty τ)).obj P).Sat K.caseAlgebra (compileTwoExit e) ↔
      K.satTwoExit e :=
  sat_compileTwoExit_proof K e

/-- Every already validated algebra admits the two-exit comparison with the
same expansion and the same operation presentation. -/
theorem sat_compileTwoExit_validated (A : ValidatedCaseAlgebra J P) (e : TwoExitEquation P) :
    ((LetCase.inst (Ctx.nil : Ctx Empty τ)).obj P).Sat A.algebra (compileTwoExit e) ↔
      A.expand.satTwoExit e :=
  (Iff.of_eq (congrArg (fun B =>
    ((LetCase.inst (Ctx.nil : Ctx Empty τ)).obj P).Sat B (compileTwoExit e))
    A.presentation.symm)).trans (sat_compileTwoExit A.expand e)

end Silmaril.Isotope.Institution.Acyclic
