module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Proofs

universe u v w x

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}

private theorem iterate_mono {F : Ty V S → Type x} {carried : Ports (Ty V S)}
    (left right : Tuple F carried → Option (Tuple F (Theta.BodyResults carried)))
    (branch : F (.control 2) → Bool)
    (body : ∀ i o, left i = some o → right i = some o)
    (n n' : Nat) (enough : n ≤ n') (input output : Tuple F carried)
    (returns : NestedTheta.iterate left branch n input = some output) :
    NestedTheta.iterate right branch n' input = some output := by
  induction n generalizing n' input with
  | zero => cases returns
  | succ n ih =>
    cases n' with
    | zero => omega
    | succ n' =>
      cases run : left input with
      | none => simp [NestedTheta.iterate, run] at returns
      | some tuple =>
        cases tuple with
        | cons selector next =>
          have large := body _ _ run
          by_cases test : branch selector
          · have rest : NestedTheta.iterate left branch n next = some output := by
              simpa [NestedTheta.iterate, run, test] using returns
            simpa [NestedTheta.iterate, large, test] using
              ih n' (Nat.le_of_succ_le_succ enough) next rest
          · simpa [NestedTheta.iterate, large, test] using
              (show some next = some output by
                simpa [NestedTheta.iterate, run, test] using returns)

private def Preserves (m : Machine.{u, v, w} Op) (low high : Handler m) : Prop :=
  ∀ {ins outs : Ports (Ty V S)} (op : Instruction Op ins outs) (input : Tuple m.Val ins)
    (output : Tuple m.Val outs), low op input = some output → high op input = some output

private theorem evalKind_mono (m : Machine.{u, v, w} Op) {ins outs : Ports (Ty V S)}
    (kind : NestedTheta.Kind (Instruction Op) ins outs) (low high : Handler m)
    (preserves : Preserves m low high) {loops loops' : Nat} (enough : loops ≤ loops')
    (body body' : Fin kind.arity → Tuple m.Val kind.entry → Option (Tuple m.Val kind.exit))
    (children : ∀ k i o, body k i = some o → body' k i = some o)
    (input : Tuple m.Val ins) (output : Tuple m.Val outs)
    (returns : evalKind m low loops kind body input = some output) :
    evalKind m high loops' kind body' input = some output := by
  cases kind with
  | base shape =>
    cases shape with
    | simple opcode => exact preserves opcode input output returns
    | gamma extra => cases input with | cons tag entry => exact children tag.selector entry output returns
  | theta =>
    exact iterate_mono (body (0 : Fin 1)) (body' (0 : Fin 1)) _
      (children (0 : Fin 1)) _ _ enough input output returns

private theorem evalBody_mono (m : Machine.{u, v, w} Op) (low high : Handler m)
    (preserves : Preserves m low high) {loops loops' : Nat} (enough : loops ≤ loops')
    {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
    (term : NestedTheta.Term (Instruction Op) args past sigs outs)
    (input : Tuple m.Val args) (locals : Locals m.Val past) (output : Tuple m.Val outs)
    (returns : evalBody m low loops term input locals = some output) :
    evalBody m high loops' term input locals = some output := by
  induction term with
  | ret => exact returns
  | bind node children rest childIH restIH =>
    simp only [evalBody] at returns ⊢
    cases run : evalKind m low loops node.kind
        (fun k i => evalBody m low loops (past := []) (children k) i PUnit.unit)
        (node.inputs.read input locals) with
    | none => rw [run] at returns; cases returns
    | some value =>
      rw [run] at returns
      have run' := evalKind_mono m node.kind low high preserves enough _ _
        (fun k i o => childIH k i PUnit.unit o) _ _ run
      rw [run']
      exact restIH input (locals.snoc value) output returns

theorem invoke_mono (m : Machine.{u, v, w} Op) {loops loops' : Nat} (enoughLoops : loops ≤ loops')
    (calls calls' : Nat) (enoughCalls : calls ≤ calls') :
    ∀ {params results : Ports (Ty V S)} (callee : m.Val (.value (.function params results)))
      (input : Tuple m.Val params) (output : Tuple m.Val results),
      invoke m loops calls callee input = some output →
      invoke m loops' calls' callee input = some output := by
  induction calls generalizing calls' with
  | zero =>
    intro params results callee input output impossible
    cases impossible
  | succ calls ih =>
    cases calls' with
    | zero => omega
    | succ calls' =>
      intro params results callee input output returns
      have handlers : Preserves m (dispatch m (invoke m loops calls))
          (dispatch m (invoke m loops' calls')) := by
        intro ins outs opcode values answer done
        cases opcode with
        | primitive op => exact done
        | apply fn =>
          cases values with
          | cons callee arguments => exact ih calls' (Nat.le_of_succ_le_succ enoughCalls) callee arguments answer done
      cases callee with
      | closure values body =>
        exact evalBody_mono m _ _ handlers enoughLoops body.toTerm _ PUnit.unit output returns

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Proofs
