module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Defs
public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms
public import Silmaril.SSA.RVSDG.Theta.Thms
import Silmaril.Proofs.SSA.RVSDG.OrderedRuntime.Structured.Theta.Adequacy

/-! # Total-body adequacy for ordered runtime feedback -/

public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta

open CategoryTheory Silmaril.Elgot

universe u v w k
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {carried : Ports (Ty V)} {sigs : List (Ports (Ty V))}
variable {ρ : Type (max u w)}

/-- The categorical loop computes the given Elgot monad's iteration. -/
theorem close_of {N : Type k → Type k} [_root_.Monad N] [LawfulMonad N] [Iterate N]
    {A : Type k} (f : A → N (A ⊕ A)) : ⇑(close f).of = iter f :=
  Proofs.close_of f

variable (m : Model P E (StateM ρ)) (g : Loop (P := P) (E := E) (carried := carried) (sigs := sigs))
variable {data : Data carried} (checked : BodyChecked data g)

/-- For a total body, all returned tuples of the computation, including
its last runtime, coincide with the numbered θ execution. -/
theorem mem_denoteTotal (input output : Tuple (RuntimeValues m.value ρ) (Threaded carried)) :
    output ∈ denoteTotal m g checked input ↔ g.Returns m.toRVSDG input output :=
  Proofs.mem_denote m g checked input output

theorem denoteTotal_eq_some (input output : Tuple (RuntimeValues m.value ρ) (Threaded carried)) :
    denoteTotal m g checked input = _root_.Part.some output ↔ g.Returns m.toRVSDG input output :=
  _root_.Part.eq_some_iff.trans (mem_denoteTotal m g checked input output)

/-- Undefinedness is exactly infinite continuation of a total body. -/
theorem denoteTotal_eq_none (input : Tuple (RuntimeValues m.value ρ) (Threaded carried)) :
    denoteTotal m g checked input = _root_.Part.none ↔ g.Diverges m.toRVSDG input :=
  Proofs.none_iff m g checked input

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta
