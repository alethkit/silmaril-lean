module

public import Silmaril.SSA.SeaOfNodes.MLIR.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.MLIR.Proofs

open RVSDG (Port Tuple Origin Wires Locals extend)
open Diamond (Dataflow Val dataPorts)
open Silmaril.MLIR.Arith (Block Env Width)
open Lowering

variable {Γ : List Width} {args : List (Diamond.Ty Width)} {past sigs : List (List (Diamond.Ty Width))}
variable {w v : Width}

private def Agrees (env : Env Γ) {ports : List (Diamond.Ty Width)}
    (names : Tuple (Names Γ) ports) (values : Tuple (Val Word) ports) : Prop :=
  ∀ {w : Width} (p : Port ports (.value (.data w))), env.get (names.get p) = values.get p

private def LocalsAgree (env : Env Γ) : {past : List (List (Diamond.Ty Width))} →
    Locals (Names Γ) past → Locals (Val Word) past → Prop
  | [], _, _ => True
  | _ :: _, names, values => Agrees env names.1 values.1 ∧ LocalsAgree env names.2 values.2

private theorem get_map {ports : List (Diamond.Ty Width)} {t : Diamond.Ty Width}
    (names : Tuple (Names Γ) ports) (p : Port ports t) :
    (names.map (weaken v)).get p = weaken v t (names.get p) := by
  induction p with
  | head => cases names; rfl
  | tail p ih => cases names with | cons _ tail => exact ih tail

private theorem weaken_get {ports : List (Diamond.Ty Width)} (names : Tuple (Names Γ) ports)
    (p : Port ports (.value (.data w))) (env : Env Γ) (value : Word v) :
    (Env.cons value env).get ((names.map (weaken v)).get p) = env.get (names.get p) := by
  rw [get_map]
  rfl

private theorem inputs_agree (env : Env Γ) : Agrees env (inputNames Γ) (sourceInputs env) := by
  induction env with
  | nil => intro _ p; cases p
  | cons value env ih =>
    intro _ p
    cases p with
    | head => rfl
    | tail p => exact (weaken_get _ p env value).trans (ih p)

private theorem locals_get (env : Env Γ) (names : Locals (Names Γ) past)
    (values : Locals (Val Word) past) (h : LocalsAgree env names values) (i : Fin past.length) :
    Agrees env (names.get i) (values.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons ports tail ih =>
    exact Fin.cases h.1 (fun j => ih names.2 values.2 h.2 j) i

private theorem push_agree (env : Env Γ) (names : Locals (Names Γ) past)
    (values : Locals (Val Word) past) (h : LocalsAgree env names values) (value : Word v) :
    LocalsAgree (.cons value env) (pushLocal v names) (values.snoc (.cons value .nil)) := by
  induction past with
  | nil =>
    refine ⟨?_, trivial⟩
    intro _ p
    cases p with
    | head => rfl
    | tail p => cases p
  | cons _ _ ih =>
    exact ⟨fun p => (weaken_get _ p env value).trans (h.1 p), ih names.2 values.2 h.2⟩

private theorem resolve_correct (scope : Scope args past Γ) (env : Env Γ)
    (entry : Tuple (Val Word) args) (locals : Locals (Val Word) past)
    (hi : Agrees env scope.inputs entry) (hl : LocalsAgree env scope.locals locals)
    (wire : Origin args past (.value (.data w))) :
    env.get (scope.resolve wire) = Diamond.read model wire entry locals := by
  cases wire with
  | arg p => exact hi p
  | output i p => exact locals_get env scope.locals locals hl i p

private theorem emit_correct (scope : Scope args past Γ) (env : Env Γ)
    (entry : Tuple (Val Word) args) (locals : Locals (Val Word) past)
    (hi : Agrees env scope.inputs entry) (hl : LocalsAgree env scope.locals locals)
    {ins : List (Diamond.ValueSort Width)} (op : Op ins (.data w))
    (wires : Wires args past (dataPorts ins)) :
    (emit scope op wires).denote env = model.run op (wires.read entry locals) := by
  cases op with
  | constant value => cases wires; rfl
  | binary op =>
    cases wires with | cons x tail =>
    cases tail with | cons y tail =>
    cases tail
    have hx := resolve_correct scope env entry locals hi hl x
    have hy := resolve_correct scope env entry locals hi hl y
    cases op <;>
      (change _ = _; simp only [emit, Silmaril.MLIR.Arith.Rhs.denote,
        Silmaril.MLIR.Arith.BinOp.denote, hx, hy]; rfl)

private theorem lowerFrom_correct (flow : Dataflow Op args past sigs)
    (scope : Scope args past Γ) (env : Env Γ)
    (entry : Tuple (Val Word) args) (locals : Locals (Val Word) past)
    (hi : Agrees env scope.inputs entry) (hl : LocalsAgree env scope.locals locals)
    (result : Origin args (extend past sigs) (.value (.data w))) :
    (lowerFrom flow scope result).denote env =
      Diamond.read model result entry (flow.eval model entry locals) := by
  induction flow generalizing Γ with
  | nil => exact resolve_correct scope env entry locals hi hl result
  | cons op wires rest ih =>
    cases op <;>
      (simp only [lowerFrom, Block.denote, Dataflow.eval, emit_correct scope env entry locals hi hl]
       apply ih
       · exact fun p => (weaken_get _ p _ _).trans (hi p)
       · exact push_agree _ _ _ hl _)

theorem lower_denote (flow : Dataflow Op (inputPorts Γ) [] sigs)
    (result : Origin (inputPorts Γ) (extend [] sigs) (.value (.data w))) (env : Env Γ) :
    (lower flow result).denote env =
      Diamond.read model result (sourceInputs env) (flow.eval model (sourceInputs env) PUnit.unit) :=
  lowerFrom_correct flow _ env (sourceInputs env) PUnit.unit (inputs_agree env) trivial result

end Silmaril.SSA.SeaOfNodes.MLIR.Proofs
