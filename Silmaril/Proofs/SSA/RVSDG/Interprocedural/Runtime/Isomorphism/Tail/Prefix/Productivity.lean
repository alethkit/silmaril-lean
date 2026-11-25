module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {outs : Ports (Ty V S)} {left right : Activation m outs}

private theorem hasReturn_iff (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids left right) :
    (∃ out, Returns m left.job out) ↔ ∃ out, Returns m right.job out := by
  cases paired with
  | intro callee inputs =>
    simpa only [Activation.job, and_true] using
      (Recursive.call_returns_iff respects callee inputs (observesL := fun _ => True)
        (observesR := fun _ => True) (fun _ _ _ => Iff.rfl))

theorem diverges_iff (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids left right)
    (supportedL : SupportedFrom m left) (supportedR : SupportedFrom m right) :
    Diverges m left ↔ Diverges m right := by
  have returns := hasReturn_iff respects paired
  constructor
  · intro infinite
    exact diverges_of_supported_no_return supportedR fun out h =>
      let ⟨value, returnsLeft⟩ := returns.mpr ⟨out, h⟩
      diverges_no_return infinite value returnsLeft
  · intro infinite
    exact diverges_of_supported_no_return supportedL fun out h =>
      let ⟨value, returnsRight⟩ := returns.mp ⟨out, h⟩
      diverges_no_return infinite value returnsRight

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Proofs
