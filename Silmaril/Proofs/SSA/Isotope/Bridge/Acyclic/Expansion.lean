module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Defs

public section
set_option backward.isDefEq.respectTransparency false

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Logic.Institution (Corridor)
open LetIter.Semantics.Categorical (TypeModel InstructionModel boundVar)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V] {J : V ⥤ C}
  (M : TypeModel τ V)

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

private theorem singletonInput_project (A : τ) :
    singletonInput M A ≫ boundVar M (Γ := Γ₀) (β := .snoc .nil A) 0 = 𝟙 (M.obj A) := by
  change ((λ_ (M.obj A)).inv ≫ (λ_ (𝟙_ V ⊗ M.obj A)).inv) ≫
    (CartesianMonoidalCategory.snd _ _ ≫ CartesianMonoidalCategory.snd _ _) = _
  simp [Category.assoc]

variable [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Readback

variable [DistributiveFreydCategory J]

theorem readInstructions_freyd_proof (I : InstructionModel J M P.Instr) :
    readInstructions J M (freydCaseAlgebra J M I) rfl = I := by
  cases I with
  | mk arrows =>
    unfold readInstructions
    congr 1
    funext f
    change J.map (singletonInput M (instrSrc f)) ≫
      (J.map (boundVar M (Γ := Γ₀) (β := .snoc .nil (instrSrc f)) 0) ≫ arrows f) = arrows f
    rw [← J.map_comp_assoc, singletonInput_project, J.map_id, Category.id_comp]

theorem freydPresentation_iff_proof (A : CaseAlgebra P) (h : A.Carrier = freydCaseArrow J M) :
    (∃ I, freydCaseAlgebra J M I = A) ↔
      freydCaseAlgebra J M (readInstructions J M A h) = A := by
  constructor
  · rintro ⟨I, rfl⟩
    rw [readInstructions_freyd_proof]
  · intro e
    exact ⟨_, e⟩

end Readback

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

theorem exactExpansion_iff_proof (A : CaseAlgebra P) :
    (∃ K : CoherentRegionModel J P, K.caseAlgebra = A) ↔
      ∃ (M : TypeModel τ V) (h : A.Carrier = freydCaseArrow J M),
        freydCaseAlgebra J M (readInstructions J M A h) = A ∧
        (letI := readInstructions J M A h; RegionTypingCoherent (Φ := P.Instr) J M) := by
  constructor
  · rintro ⟨K, rfl⟩
    refine ⟨K.types, rfl, ?_⟩
    change freydCaseAlgebra J K.types
        (readInstructions J K.types (freydCaseAlgebra J K.types K.instructions) rfl) = _ ∧
      (letI := readInstructions J K.types (freydCaseAlgebra J K.types K.instructions) rfl
       RegionTypingCoherent (Φ := P.Instr) J K.types)
    rw [readInstructions_freyd_proof]
    exact ⟨rfl, K.coherent⟩
  · rintro ⟨M, h, operations, coherent⟩
    exact ⟨expandAlgebra J M A h coherent, operations⟩

variable [FreydCategory.CentralUnit J]

theorem entails_reify_iff_on_expansions_proof (Γ : Set (CaseEquation P)) (e : CaseEquation P) :
    (ssaRoom J P).Entails (reify '' Γ) (reify e) ↔
      ∀ A : CaseAlgebra P, (∃ K : CoherentRegionModel J P, K.caseAlgebra = A) →
        (∀ φ ∈ Γ, ((LetCase.inst Γ₀).obj P).Sat A φ) → ((LetCase.inst Γ₀).obj P).Sat A e := by
  constructor
  · intro h A hex hA
    obtain ⟨K, rfl⟩ := hex
    let N := ShrinkHoms.toShrinkHoms (Discrete.mk K)
    refine ((reifyCorridor J P).sat N e).mp (h N ?_)
    rintro _ ⟨φ, hφ, rfl⟩
    exact ((reifyCorridor J P).sat N φ).mpr (hA φ hφ)
  · intro h N hN
    let K := (ShrinkHoms.fromShrinkHoms N).as
    refine ((reifyCorridor J P).sat N e).mpr (h K.caseAlgebra ⟨K, rfl⟩ ?_)
    intro φ hφ
    exact ((reifyCorridor J P).sat N φ).mp (hN _ ⟨φ, hφ, rfl⟩)

end Silmaril.Isotope.Institution.Acyclic
