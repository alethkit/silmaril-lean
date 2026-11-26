module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Thms

/-! # Chosen categorical interpretations and model expansion -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Isotope.LetCase.LocallyNameless
open LambdaSSA.Acyclic (Code contextMap)
open LetIter.Semantics.Categorical (TypeModel InstructionModel envObj boundVar)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent ctxObj labelObj labelInject)
open Theory (TypingIndex)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V] (J : V ⥤ C)
  (M : TypeModel τ V)

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- Insert a value into the singleton bound context of the exact LetCase room. -/
def singletonInput (A : τ) : M.obj A ⟶ envObj M Γ₀ (.snoc .nil A) :=
  (λ_ (M.obj A)).inv ≫ (λ_ (𝟙_ V ⊗ M.obj A)).inv

/-- Recover the primitive arrow by applying the algebra's operation to the
newest bound variable and removing the two empty context factors. -/
@[instance_reducible] noncomputable def readInstructions (A : CaseAlgebra P)
    (carriers : A.Carrier = freydCaseArrow J M) : InstructionModel J M P.Instr where
  denote f :=
    let β : BoundCtx τ 1 := .snoc .nil (instrSrc f)
    let src : TypingIndex τ := ⟨1, β, instrSrc f⟩
    let dst : TypingIndex τ := ⟨1, β, instrTrg f⟩
    let variableArrow := J.map (boundVar M (Γ := Γ₀) (β := β) 0)
    J.map (singletonInput M (instrSrc f)) ≫
      cast (congrFun carriers dst)
        (A.op (.op (β := β) f) (fun _ => cast (congrFun carriers src).symm variableArrow))

variable [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]

/-- Interpret exact single-exit code on the SSA context and exit objects by
eliminating acyclic joins as LetCase binders. -/
noncomputable def denoteAcyclic [DistributiveFreydCategory J]
    (I : InstructionModel J M P.Instr) {n : Nat} {β : BoundCtx τ n} {A : τ}
    (c : Code P.Instr β A) : J.obj (ctxObj M β.toList) ⟶ J.obj (labelObj M [A]) :=
  letI := I
  J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M c.toLetCase.2 ≫
    J.map (labelInject M (L := [A]) 0 rfl)

variable
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- Use the chosen Freyd interpretation in the existing exact SSA room when
the ambient iteration and region typing coherence have been supplied. -/
def expandFreyd (I : InstructionModel J M P.Instr)
    (coherent : letI := I; RegionTypingCoherent (Φ := P.Instr) J M) : CoherentRegionModel J P :=
  ⟨M, I, coherent⟩

/-- Use the primitive arrows recovered from the algebra in the coherent
region model. Agreement of all operations gives the section law. -/
noncomputable def expandAlgebra (A : CaseAlgebra P) (h : A.Carrier = freydCaseArrow J M)
    (coherent : letI := readInstructions J M A h; RegionTypingCoherent (Φ := P.Instr) J M) :
    CoherentRegionModel J P :=
  expandFreyd J M (readInstructions J M A h) coherent

end Silmaril.Isotope.Institution.Acyclic
