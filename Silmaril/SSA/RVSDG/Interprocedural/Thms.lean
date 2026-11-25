module

public import Silmaril.SSA.RVSDG.Interprocedural.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Scoping

public section

namespace Silmaril.SSA.RVSDG.Interprocedural

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args : Ports (Ty V S)} {past : List (Ports (Ty V S))}
variable {members : List (Function V S)}

/-- A physical λ-to-λ capture wire in the φ region has an earlier producer.
The separate recursion arguments can be used by every member. -/
theorem Phi.capture_producer_lt (phi : Phi Op args past members) (i : Fin members.length)
    {t : Ty V S} (port : Port (phi.definitions i).context t) {producer : Nat}
    (h : ((phi.definitions i).captures.get port).producer = some producer) :
    producer < i.val :=
  Proofs.capture_producer_lt phi i port h

theorem Phi.resultOrigin_producer (phi : Phi Op args past members) (i : Fin members.length) :
    (phi.resultOrigin i).producer = some i.val :=
  rfl

end Silmaril.SSA.RVSDG.Interprocedural
