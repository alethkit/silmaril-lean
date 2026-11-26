module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Opcode.Defs

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Proofs

open OrderedRuntime.Structured (Data Threaded)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

omit [TypeFormers τ] in
private theorem instruction_eq {A B : τ} {p q : TwoBlock.Instruction Φ A B} (h : p.op = q.op) : p = q := by
  cases p
  cases q
  cases h
  rfl

private structure Packed (Φ : Type u) [HasTy Φ τ] where
  ins : Ports (OrderedRuntime.Structured.Ty τ)
  outs : Ports (OrderedRuntime.Structured.Ty τ)
  inData : Data ins
  outData : Data outs
  effect : Effect Φ ins outs

private def Packed.toOpcode (p : Packed (τ := τ) Φ) :
    Σ i o : Ports (OrderedRuntime.Structured.Ty τ), Op Φ i o :=
  ⟨Threaded p.ins, Threaded p.outs, .ordered p.inData p.outData (.effect p.effect)⟩

private theorem packed_injective {p q : Packed (τ := τ) Φ}
    (h : opcodeKey p.toOpcode.2.2 = opcodeKey q.toOpcode.2.2) : p = q := by
  obtain ⟨i, o, a, b, op⟩ := p
  obtain ⟨i', o', a', b', op'⟩ := q
  cases op <;> cases op' <;> simp [Packed.toOpcode, opcodeKey, effectKey] at h
  all_goals
    first
    | obtain ⟨rfl, rfl, rfl, rfl, op⟩ := h
      rw [instruction_eq op]
    | obtain ⟨rfl, rfl, op⟩ := h
      rw [instruction_eq op]

theorem opcode_injective {i o : Ports (OrderedRuntime.Structured.Ty τ)}
    (p q : Op Φ i o) (h : opcodeKey p = opcodeKey q) : p = q := by
  have packed {i o i' o' : Ports (OrderedRuntime.Structured.Ty τ)} (x : Op Φ i o) (y : Op Φ i' o')
      (h : opcodeKey x = opcodeKey y) :
      (⟨i, o, x⟩ : Σ i o, Op Φ i o) = ⟨i', o', y⟩ := by
    cases x with
    | ordered a b x =>
      cases y with
      | ordered a' b' y =>
        cases x with
        | pure x => exact nomatch x
        | effect x =>
          cases y with
          | pure y => exact nomatch y
          | effect y =>
            exact congrArg Packed.toOpcode
              (packed_injective (p := ⟨_, _, a, b, x⟩) (q := ⟨_, _, a', b', y⟩) h)
  exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj (packed p q h)).2)).2

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Proofs
