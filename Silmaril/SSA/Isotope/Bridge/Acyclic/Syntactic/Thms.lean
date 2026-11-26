module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.SyntacticRoundTrip

/-! # Syntactic round trip through the existing LetCase bridge -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Code

open Region
open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {n : Nat} {β : BoundCtx τ n} {A : τ}

theorem guardedSSA_valueBranches (c : Code Φ β A)
    {L : LCtx τ} {exit : Nat} (hi : At L exit A) : ValueBranches β.toList (c.guardedSSA exit) L :=
  Proofs.SSA.Isotope.Bridge.Acyclic.SyntacticRoundTrip.guarded_typed c hi

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => RoundTripSeed (τ := τ) (Φ := Φ) pe

/-- Compile structured SSA to the existing exact LetCase term and reify it
as SSA. After branch binding, the admitted code is equivalent to its round
trip in the contextual extension by unary return fusion and case returns. -/
theorem syntactic_roundTrip (c : Code Φ β A) (hc : c.Admitted)
    {L : LCtx τ} {exit : Nat} (hi : At L exit A) :
    Paper.Extension.Eqv Seed β.toList
      (c.guardedSSA exit) ((ofLetCase c.toLetCase.2).guardedSSA exit) L :=
  Proofs.SSA.Isotope.Bridge.Acyclic.SyntacticRoundTrip.code pe c hc hi

/-- A source that already has constructor-valued branches belongs to the
same class before inserting the branch bindings. -/
theorem syntactic_roundTrip_of_valueBranches (c : Code Φ β A) (hc : c.Admitted)
    {L : LCtx τ} {exit : Nat} (hi : At L exit A) (hr : ValueBranches β.toList (c.toSSA exit) L) :
    Paper.Extension.Eqv Seed β.toList
      (c.toSSA exit) ((ofLetCase c.toLetCase.2).guardedSSA exit) L :=
  (Paper.Extension.Eqv.paper (.cfgEta (.native hr.bindBranchArguments_equiv))).trans (c.syntactic_roundTrip pe hc hi)

/-- At the singleton interface, the exact guarded source and the bound round
trip are the same arrow in the optional syntax quotient. -/
theorem singleton_syntactic_roundTrip {X B : τ}
    (c : Code Φ ((BoundCtx.nil : BoundCtx τ 0).snoc X) B) (hc : c.Admitted)
    (hr : ValueBranches [X] (c.toSSA 0) [B]) :
    (Paper.Extension.Singleton.projection Seed).map (Paper.TypeCategory.ofRegion hr) =
      Paper.Extension.Singleton.ofRegion Seed
        ((ofLetCase c.toLetCase.2).guardedSSA_valueBranches (rfl : At [B] 0 B)) :=
  (Paper.Extension.Singleton.ofRegion_eq_iff _ hr _).2
    (c.syntactic_roundTrip_of_valueBranches pe hc rfl hr)

end Silmaril.Isotope.LambdaSSA.Acyclic.Code

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Operand

open Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {n : Nat} {β : BoundCtx τ n} {A : τ} {ε : Type w} [HasEff Φ ε]

/-- The guarded return of an admitted expression is equivalent to the
guarded structured code reified from that exact LetCase operand. -/
theorem syntactic_roundTrip (pe : ε) (a : Operand Φ β A) (ha : a.Admitted)
    {L : LCtx τ} {exit : Nat} (hi : At L exit A) :
    Paper.Extension.Eqv (RoundTripSeed pe) β.toList
      ((Code.br a).guardedSSA exit) ((Code.ofLetCase a.2).guardedSSA exit) L :=
  Proofs.SSA.Isotope.Bridge.Acyclic.SyntacticRoundTrip.operand pe a.2 ha hi

end Silmaril.Isotope.LambdaSSA.Acyclic.Operand
