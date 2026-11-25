module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Invocation
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}

theorem call_returns_iff (respects : PrimitivesRespect m ids)
    {params results : Ports (Ty V S)} {calleeL calleeR : m.Val (.value (.function params results))}
    (callees : ValueRelated m ids calleeL calleeR) {inL inR : Tuple m.Val params}
    (inputs : TupleRelated m ids inL inR) {observesL observesR : Tuple m.Val results → Prop}
    (observation : ∀ x y, TupleRelated m ids x y → (observesL x ↔ observesR y)) :
    (∃ out, Recursive.Returns m (.call calleeL inL) out ∧ observesL out) ↔
      ∃ out, Recursive.Returns m (.call calleeR inR) out ∧ observesR out := by
  constructor
  · rintro ⟨outL, returns, observed⟩
    obtain ⟨loops, depth, runL⟩ := (Recursive.call_iff m calleeL inL outL).1 returns
    have paired := invoke_related respects loops depth callees inputs
    rw [runL] at paired
    obtain ⟨outR, runR, outputs⟩ : ∃ outR, invoke m loops depth calleeR inR = some outR ∧
        TupleRelated m ids outL outR := by
      generalize invoke m loops depth calleeR inR = run at paired ⊢
      cases paired with
      | some outputs => exact ⟨_, rfl, outputs⟩
    exact ⟨outR, (Recursive.call_iff m calleeR inR outR).2 ⟨loops, depth, runR⟩,
      (observation outL outR outputs).1 observed⟩
  · rintro ⟨outR, returns, observed⟩
    obtain ⟨loops, depth, runR⟩ := (Recursive.call_iff m calleeR inR outR).1 returns
    have paired := invoke_related respects loops depth callees inputs
    rw [runR] at paired
    obtain ⟨outL, runL, outputs⟩ : ∃ outL, invoke m loops depth calleeL inL = some outL ∧
        TupleRelated m ids outL outR := by
      generalize invoke m loops depth calleeL inL = run at paired ⊢
      cases paired with
      | some outputs => exact ⟨_, rfl, outputs⟩
    exact ⟨outL, (Recursive.call_iff m calleeL inL outL).2 ⟨loops, depth, runL⟩,
      (observation outL outR outputs).2 observed⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs
