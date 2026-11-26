module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Institution.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LambdaSSA.Acyclic (Code FiniteExit)
open LambdaSSA.Semantics.Categorical (denoteRegion packLabelExit unpackLabelExit packLabelExit_unpackLabelExit)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ) [h.PreservesProducts] [h.PreservesSums]

theorem mapFiniteExit_id_proof (e : FiniteExitEquation P) :
    mapFiniteExit (P := P) (Q := P) SignatureMap.id e = e := by
  obtain ⟨⟨n, β, L⟩, a, b⟩ := e
  have ha := a.mapSignature_id_heq
  have hb := b.mapSignature_id_heq
  unfold mapFiniteExit
  congr! (config := .unfoldSameFun) 2 <;> simp [SignatureMap.id]

theorem mapFiniteExit_comp_proof (e : FiniteExitEquation P) :
    mapFiniteExit (h.comp g) e = mapFiniteExit h (mapFiniteExit g e) := by
  obtain ⟨⟨n, β, L⟩, a, b⟩ := e
  have ha := a.mapSignature_comp_heq g h
  have hb := b.mapSignature_comp_heq g h
  unfold mapFiniteExit
  congr! (config := .unfoldSameFun) 2 <;> simp [SignatureMap.comp]

private theorem packed_equation_congr {n : Nat} {β : BoundCtx υ n} {A B : υ}
    (e : A = B) {a b : Code Q.Instr β A} {a' b' : Code Q.Instr β B}
    (ha : HEq a a') (hb : HEq b b') :
    (⟨⟨n, β, A⟩, a, b⟩ : SSAEquation Q) = ⟨⟨n, β, B⟩, a', b'⟩ := by
  cases e
  cases eq_of_heq ha
  cases eq_of_heq hb
  rfl

theorem encodeFiniteExit_map_proof (e : FiniteExitEquation P) :
    encodeFiniteExit (mapFiniteExit g e) = mapSSASignature g (encodeFiniteExit e) := by
  obtain ⟨⟨n, β, L⟩, a, b⟩ := e
  exact packed_equation_congr (FiniteExit.packedExitType_map g L).symm
    (a.encode_mapSignature_heq g).symm (b.encode_mapSignature_heq g).symm

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

omit [TypeFormers τ] [TypeFormers υ] in
private theorem boundCtx_map_toList (f : τ → υ) {n : Nat} (β : BoundCtx τ n) :
    (β.mapTypes f).toList = β.toList.map f := by
  induction β with
  | nil => rfl
  | snoc β A ih => exact congrArg (List.cons (f A)) ih

private theorem denote_congr (M : TypeModel υ V) [InstructionModel J M Q.Instr]
    {Γ Γ' L : List υ} {r r' : LambdaSSA.Region Q.Instr} (ctx : Γ = Γ') (code : r = r')
    (h : LambdaSSA.Region.HasType Γ r L) (h' : LambdaSSA.Region.HasType Γ' r' L) :
    HEq (denoteRegion J M h) (denoteRegion J M h') := by
  cases ctx
  cases code
  rfl

theorem denoteFiniteExit_pullback_proof (K : CoherentRegionModel J Q)
    {n : Nat} {β : BoundCtx τ n} {L : List τ} (c : FiniteExit P.Instr L β) :
    HEq ((K.pullbackOfWitness g (regionWitnessPullback g K)).denoteFiniteExit J c)
      (K.denoteFiniteExit J (c.mapSignature g)) := by
  let _ := K.instructions
  exact (K.denoteRegion_pullback g (regionWitnessPullback g K) c.toSSA_hasType).trans
    (denote_congr K.types (boundCtx_map_toList g.ty β).symm
      (FiniteExit.toSSA_mapSignature g c).symm (mapRegionTyping g c.toSSA_hasType)
      (c.mapSignature g).toSSA_hasType)

variable [FreydCategory.CentralUnit J]

theorem sat_encodeFiniteExit_proof (K : (ssaRoom J P).Mod) (e : FiniteExitEquation P) :
    (ssaRoom J P).Sat K (encodeFiniteExit e) ↔ (finiteExitRoom J P).Sat K e := by
  let M := K.fromShrinkHoms.as.types
  let _ := K.fromShrinkHoms.as.instructions
  let _ := K.fromShrinkHoms.as.coherent
  change denoteRegion J M (e.2.1.encode.toSSA_hasType (L := [_]) (exit := 0) rfl) =
    denoteRegion J M (e.2.2.encode.toSSA_hasType (L := [_]) (exit := 0) rfl) ↔
    denoteRegion J M e.2.1.toSSA_hasType = denoteRegion J M e.2.2.toSSA_hasType
  rw [FiniteExit.denote_encode, FiniteExit.denote_encode]
  constructor
  · intro h
    have eq := congrArg (fun f => f ≫ J.map (unpackLabelExit M e.1.exits)) h
    simpa only [Category.assoc, ← J.map_comp, packLabelExit_unpackLabelExit,
      J.map_id, Category.comp_id] using eq
  · exact fun h => congrArg (fun f => f ≫ J.map (packLabelExit M e.1.exits)) h

end Silmaril.Isotope.Institution.Acyclic
