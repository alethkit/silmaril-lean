module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Commutative.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationCommutative

/-! # Completeness of finite ranked-system comparison under the commutative schema -/

public section

universe u v w z

namespace Silmaril.Calco2019.IterationTheory

open CategoryTheory
open Silmaril.Semantics.Domain

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X Y : K}
  {C : FiniteCopowers X} {σ : Signature.{w}} {E : Type z}
  (M : Interpretation C σ E Y) {S T : Type} [Finite S] [Finite T]

/-- The commutative schema on finite copowers is a consequence of uniformity. -/
theorem FiniteCopowers.commutative_of_uniform (F : (Guardedness.greatest P).Fixpoints)
    (uniform : C.BaseUniform F) : C.CommutativeIdentities F :=
  Proofs.IterationCommutative.commutative_of_uniform F uniform

/-- The Conway laws and commutative schema transport solutions of ranked
systems along any equation-preserving finite state map. -/
theorem Interpretation.solution_of_commutative_map (F : (Guardedness.greatest P).Conway)
    (commutative : C.CommutativeIdentities F.toFixpoints)
    {g : System σ E S} {h : System σ E T} {p : S → T}
    (hom : PreservesEquations g h p) (s : S) :
    M.solution F.toFixpoints g s = M.solution F.toFixpoints h (p s) :=
  Proofs.IterationCommutative.solution_commutative_map M F commutative hom s

/-- Equality of finite ranked systems in the standard pointed path model
implies equality in every total Conway interpretation with the commutative schema. -/
theorem Interpretation.solution_of_standard_commutative (F : (Guardedness.greatest P).Conway)
    (commutative : C.CommutativeIdentities F.toFixpoints)
    (g : System σ E S) (h : System σ E T) (s : S) (t : T)
    (same : fix (update g) s = fix (update h) t) :
    M.solution F.toFixpoints g s = M.solution F.toFixpoints h t :=
  Proofs.IterationCommutative.solution_standard_commutative M F commutative g h s t same

end Silmaril.Calco2019.IterationTheory
