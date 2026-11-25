module

public import Silmaril.SSA.RVSDG.Interprocedural.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Proofs

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args : Ports (Ty V S)} {past : List (Ports (Ty V S))}
variable {members : List (Function V S)}

theorem capture_producer_lt (phi : Phi Op args past members) (i : Fin members.length)
    {t : Ty V S} (port : Port (phi.definitions i).context t) {producer : Nat}
    (h : ((phi.definitions i).captures.get port).producer = some producer) :
    producer < i.val := by
  cases source : (phi.definitions i).captures.get port with
  | arg p => simp [source, Origin.producer] at h
  | output k p =>
    have index : k.val = producer := by simpa [source, Origin.producer] using h
    have lengthBound : (memberOutputs (members.take i.val)).length ≤ i.val := by
      simp [memberOutputs, List.length_take]
    exact index ▸ Nat.lt_of_lt_of_le k.isLt lengthBound

end Silmaril.SSA.RVSDG.Interprocedural.Proofs
