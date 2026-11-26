module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Defs

public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Proofs

open NestedTheta.Institution
open OrderedRuntime.Structured (Values)

universe u v w
variable {V : Type u} {A : Stateless.Signature.{u,v} V}
variable {args ins outs carried : Ports (PortSort V)} {scope past sigs : List (Ports (PortSort V))}

private theorem bindOperands_read {F : PortSort V → Type w} (wires : Wires args past outs)
    (input : Tuple F args) (locals : Locals F past) :
    (bindOperands wires).read .nil (input, locals) = wires.read input locals := by
  induction wires with
  | nil => rfl
  | cons wire tail ih => cases wire <;> exact congrArg (Tuple.cons _) ih

private theorem feedbackReturns_iff (m : Stateless.Model.{u,v,w} A)
    (body : Tuple (Values m.value) carried → Tuple (Values m.value) (.control 2 :: carried) → Prop)
    (input output : Tuple (Values m.value) carried) :
    FeedbackReturns body input output ↔
      Theta.Iterate (fun x again y => body x (NestedTheta.Partial.tagged m.partial again y)) input output := by
  constructor
  · rintro ⟨last, path, finish⟩
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact .stop finish
    | head step _ ih => exact .again step ih
  · intro run
    induction run with
    | stop finish => exact ⟨_, .refl, finish⟩
    | again step _ ih =>
      obtain ⟨last, path, finish⟩ := ih
      exact ⟨last, path.head step, finish⟩

private theorem exec_emit_iff (m : Stateless.Model.{u,v,w} A)
    (kind : NestedTheta.Kind A.op ins carried) (operands : Operands scope ins)
    (regions : Fin kind.arity → Region A kind.entry kind.exit) (rest : Block A (scope ++ [carried]) outs)
    (env : Locals (Values m.value) scope) (output : Tuple (Values m.value) outs) :
    (emit kind operands regions rest).Exec m env output ↔
      ∃ result, NestedTheta.Partial.kindExec m.partial kind (fun i => (regions i).Returns m)
        (operands.read .nil env) result ∧ rest.Exec m (env.snoc result) output := by
  cases kind with
  | base shape =>
    cases shape with
    | simple op =>
      cases op with
      | pure op =>
        let value := m.run op (operands.read .nil env)
        constructor
        · intro run
          exact ⟨value, Part.mem_some_iff.mpr rfl, run⟩
        · rintro ⟨result, mem, run⟩
          have same : result = value := Part.mem_some_iff.mp mem
          subst result
          exact run
      | effect op => exact nomatch op
    | gamma =>
      erw [emit, Block.Exec]
      cases h : operands.read .nil env with
      | cons selector payload =>
        erw [h]
        rfl
  | theta =>
    exact exists_congr fun result => (feedbackReturns_iff m _ _ result).and Iff.rfl

theorem exec_lowerTerm_iff (m : Stateless.Model.{u,v,w} A) (t : NestedTheta.Term A.op args past sigs outs)
    (input : Tuple (Values m.value) args) (locals : Locals (Values m.value) past)
    (output : Tuple (Values m.value) outs) :
    (lowerTerm t).Exec m (input, locals) output ↔ NestedTheta.Partial.exec m.partial t input locals output := by
  induction t with
  | ret wires =>
    simp only [lowerTerm, Block.Exec, NestedTheta.Partial.exec, bindOperands_read]
    rfl
  | bind node children rest childIH restIH =>
    erw [lowerTerm, exec_emit_iff, bindOperands_read, NestedTheta.Partial.exec]
    have regions : (fun i => (lowerTerm (children i)).Returns m) =
        (fun i x y => NestedTheta.Partial.exec m.partial (children i) x PUnit.unit y) := by
      funext i x y
      exact propext (childIH i x PUnit.unit y)
    rw [regions]
    exact exists_congr fun result => Iff.rfl.and (restIH input (locals.snoc result) output)

end Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Proofs
