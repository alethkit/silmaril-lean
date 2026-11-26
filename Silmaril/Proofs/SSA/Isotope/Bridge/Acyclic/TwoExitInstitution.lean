module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Institution.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LambdaSSA.Acyclic (Code TwoExit)
open LambdaSSA.Semantics.Categorical (denoteRegion)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}

private theorem cast_equation {n : Nat} {β : BoundCtx υ n} {A B : υ} (h : A = B)
    (l r : Code Q.Instr β A) :
    (⟨⟨n, β, B⟩, h ▸ l, h ▸ r⟩ : SSAEquation Q) = ⟨⟨n, β, A⟩, l, r⟩ := by
  cases h
  rfl

theorem encodeTwoExit_map_proof (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
    [g.PreservesProducts] [g.PreservesSums] (e : TwoExitEquation P) :
    encodeTwoExit (mapTwoExit g e) = mapSSASignature g (encodeTwoExit e) := by
  rcases e with ⟨⟨n, β, A, B⟩, l, r⟩
  change (⟨⟨n, β.mapTypes g.ty, coprod (g.ty A) (g.ty B)⟩,
    (l.mapSignature g).encode, (r.mapSignature g).encode⟩ : SSAEquation Q) =
    ⟨⟨n, β.mapTypes g.ty, g.ty (coprod A B)⟩, l.encode.mapSignature g, r.encode.mapSignature g⟩
  rw [TwoExit.encode_mapSignature g l, TwoExit.encode_mapSignature g r, cast_equation]

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
    {Γ Γ' L L' : List υ} {r r' : LambdaSSA.Region Q.Instr}
    (ctx : Γ = Γ') (exits : L = L') (code : r = r')
    (h : LambdaSSA.Region.HasType Γ r L) (h' : LambdaSSA.Region.HasType Γ' r' L') :
    HEq (denoteRegion J M h) (denoteRegion J M h') := by
  cases ctx
  cases exits
  cases code
  rfl

theorem denoteTwoExit_pullback_proof (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
    [g.PreservesProducts] [g.PreservesSums] (K : CoherentRegionModel J Q)
    {n : Nat} {β : BoundCtx τ n} {A B : τ} (c : TwoExit P.Instr A B β) :
    HEq ((K.pullbackOfWitness g (regionWitnessPullback g K)).denoteTwoExit c)
      (K.denoteTwoExit (c.mapSignature g)) := by
  let _ := K.instructions
  exact (K.denoteRegion_pullback g (regionWitnessPullback g K) c.toSSA_hasType).trans
    (denote_congr K.types (boundCtx_map_toList g.ty β).symm rfl
      (TwoExit.toSSA_mapSignature g c).symm (mapRegionTyping g c.toSSA_hasType)
      (c.mapSignature g).toSSA_hasType)

variable [FreydCategory.CentralUnit J]

theorem sat_compileTwoExit_proof (K : CoherentRegionModel J P) (e : TwoExitEquation P) :
    ((LetCase.inst (Ctx.nil : Ctx Empty τ)).obj P).Sat K.caseAlgebra (compileTwoExit e) ↔
      K.satTwoExit e := by
  let _ := K.instructions
  let _ := K.coherent
  refine (sat_compile_iff K (encodeTwoExit e)).trans ?_
  change denoteRegion J K.types (e.2.1.encode.toSSA_hasType (L := [_]) (exit := 0) rfl) =
    denoteRegion J K.types (e.2.2.encode.toSSA_hasType (L := [_]) (exit := 0) rfl) ↔
    denoteRegion J K.types e.2.1.toSSA_hasType = denoteRegion J K.types e.2.2.toSSA_hasType
  rw [TwoExit.denote_encode, TwoExit.denote_encode]
  constructor
  · intro h
    have eq := congrArg (fun f => f ≫ J.map (TwoExit.unpackExit K.types e.1.left e.1.right)) h
    simpa only [Category.assoc, ← J.map_comp, TwoExit.packExit_unpackExit,
      J.map_id, Category.comp_id] using eq
  · intro h
    exact congrArg (fun f => f ≫ J.map (TwoExit.packExit K.types e.1.left e.1.right)) h

end Silmaril.Isotope.Institution.Acyclic
