module

public import Silmaril.SSA.PEG.Semantics.Defs

/-! # Typed SIMPLE source syntax and finite executions

The paper's variable contexts are ordered typed slots. An assignment binds a
fresh slot. A projection can discard the old slot to express overwrite, or
restrict both branches to a common live context. The Boolean index permits
while syntax in the source language and isolates the loop-free frontend.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}

mutual

inductive Expr (P : InstructionSet.{u,v} Data) (vars : List (Ty Data)) :
    Ty Data → Type (max u v) where
  | var {t : Ty Data} (slot : Port vars t) : Expr P vars t
  | op {ins : List (Ty Data)} {t : Ty Data}
      (instr : P ins t) (args : Args P vars ins) : Expr P vars t

inductive Args (P : InstructionSet.{u,v} Data) (vars : List (Ty Data)) :
    List (Ty Data) → Type (max u v) where
  | nil : Args P vars []
  | cons {t : Ty Data} {ts : List (Ty Data)}
      (head : Expr P vars t) (tail : Args P vars ts) : Args P vars (t :: ts)

end

inductive Stmt (P : InstructionSet.{u,v} Data) (loops : Bool) :
    List (Ty Data) → List (Ty Data) → Type (max u v) where
  | assign {vars : List (Ty Data)} {t : Ty Data} (rhs : Expr P vars t) :
      Stmt P loops vars (t :: vars)
  | project {vars outs : List (Ty Data)} (slots : Tuple (Port vars) outs) :
      Stmt P loops vars outs
  | seq {vars mid outs : List (Ty Data)}
      (first : Stmt P loops vars mid) (second : Stmt P loops mid outs) : Stmt P loops vars outs
  | branch {vars outs : List (Ty Data)}
      (guard : Expr P vars .bool) (yes no : Stmt P loops vars outs) : Stmt P loops vars outs
  | while {vars : List (Ty Data)} (enabled : loops = true) (guard : Expr P vars .bool)
      (body : Stmt P loops vars vars) : Stmt P loops vars vars

structure Program (P : InstructionSet.{u,v} Data) (loops : Bool)
    (params : List (Ty Data)) (result : Ty Data) where
  locals : List (Ty Data)
  body : Stmt P loops params locals
  retvar : Port locals result

variable (model : Interpretation.{u,v,w} P)
variable {vars : List (Ty Data)} {t : Ty Data}

mutual

def Expr.evalLift (store : Tuple model.Value vars) :
    {ty : Ty Data} → Expr P vars ty → ULift.{u} (Option (model.Value ty))
  | _, .var p => ⟨some (store.get p)⟩
  | _, .op instr args => ⟨(Args.eval store args).elim none (model.run instr)⟩

def Args.eval (store : Tuple model.Value vars) :
    {ts : List (Ty Data)} → Args P vars ts → Option (Tuple model.Value ts)
  | _, .nil => some .nil
  | _, .cons e es =>
    match (Expr.evalLift store e).down, Args.eval store es with
    | some v, some vs => some (.cons v vs)
    | _, _ => none

end

def Expr.eval (store : Tuple model.Value vars) (e : Expr P vars t) : Option (model.Value t) :=
  (e.evalLift model store).down

/-- Finite source executions. Here `none` is a finite evaluation failure.
Nontermination has no finite execution derivation. The source treats primitive
`none` as finite failure, with no trap detail supplied by the interpretation. -/
inductive Exec (model : Interpretation.{u,v,w} P) :
    {loops : Bool} → {vars outs : List (Ty Data)} →
      Stmt P loops vars outs → Tuple model.Value vars → Option (Tuple model.Value outs) → Prop where
  | assign {loops : Bool} {vars : List (Ty Data)} {t : Ty Data}
      {rhs : Expr P vars t} {store : Tuple model.Value vars} {value : model.Value t}
      (h : rhs.eval model store = some value) :
      Exec model (.assign (loops := loops) rhs) store (some (.cons value store))
  | assignFailed {loops : Bool} {vars : List (Ty Data)} {t : Ty Data}
      {rhs : Expr P vars t} {store : Tuple model.Value vars}
      (h : rhs.eval model store = none) :
      Exec model (.assign (loops := loops) rhs) store none
  | project {loops : Bool} {vars outs : List (Ty Data)} {slots : Tuple (Port vars) outs}
      {store : Tuple model.Value vars} :
      Exec model (.project (loops := loops) slots) store (some (slots.map (fun _ p => store.get p)))
  | firstFailed {loops : Bool} {vars mid outs : List (Ty Data)}
      {a : Stmt P loops vars mid} {b : Stmt P loops mid outs} {store : Tuple model.Value vars}
      (first : Exec model a store none) : Exec model (.seq a b) store none
  | seq {loops : Bool} {vars mid outs : List (Ty Data)}
      {a : Stmt P loops vars mid} {b : Stmt P loops mid outs}
      {store : Tuple model.Value vars} {next : Tuple model.Value mid}
      {result : Option (Tuple model.Value outs)}
      (first : Exec model a store (some next)) (second : Exec model b next result) :
      Exec model (.seq a b) store result
  | branchFailed {loops : Bool} {vars outs : List (Ty Data)}
      {guard : Expr P vars .bool} {yes no : Stmt P loops vars outs} {store : Tuple model.Value vars}
      (h : guard.eval model store = none) : Exec model (.branch guard yes no) store none
  | branchTrue {loops : Bool} {vars outs : List (Ty Data)}
      {guard : Expr P vars .bool} {yes no : Stmt P loops vars outs}
      {store : Tuple model.Value vars} {result : Option (Tuple model.Value outs)}
      (h : guard.eval model store = some ⟨true⟩) (arm : Exec model yes store result) :
      Exec model (.branch guard yes no) store result
  | branchFalse {loops : Bool} {vars outs : List (Ty Data)}
      {guard : Expr P vars .bool} {yes no : Stmt P loops vars outs}
      {store : Tuple model.Value vars} {result : Option (Tuple model.Value outs)}
      (h : guard.eval model store = some ⟨false⟩) (arm : Exec model no store result) :
      Exec model (.branch guard yes no) store result
  | whileGuardFailed {vars : List (Ty Data)}
      {guard : Expr P vars .bool} {body : Stmt P true vars vars} {store : Tuple model.Value vars}
      (h : guard.eval model store = none) : Exec model (.while rfl guard body) store none
  | whileStop {vars : List (Ty Data)}
      {guard : Expr P vars .bool} {body : Stmt P true vars vars} {store : Tuple model.Value vars}
      (h : guard.eval model store = some ⟨false⟩) : Exec model (.while rfl guard body) store (some store)
  | whileBodyFailed {vars : List (Ty Data)}
      {guard : Expr P vars .bool} {body : Stmt P true vars vars} {store : Tuple model.Value vars}
      (h : guard.eval model store = some ⟨true⟩) (step : Exec model body store none) :
      Exec model (.while rfl guard body) store none
  | whileStep {vars : List (Ty Data)}
      {guard : Expr P vars .bool} {body : Stmt P true vars vars}
      {store next : Tuple model.Value vars} {result : Option (Tuple model.Value vars)}
      (h : guard.eval model store = some ⟨true⟩) (step : Exec model body store (some next))
      (rest : Exec model (.while rfl guard body) next result) : Exec model (.while rfl guard body) store result

variable {loops : Bool}

def Program.Returns (p : Program P loops vars t) (input : Tuple model.Value vars)
    (value : model.Value t) : Prop :=
  ∃ final, Exec model p.body input (some final) ∧ final.get p.retvar = value

def Program.Fails (p : Program P loops vars t) (input : Tuple model.Value vars) : Prop :=
  Exec model p.body input none

def Program.Diverges (p : Program P loops vars t) (input : Tuple model.Value vars) : Prop :=
  ¬∃ outcome, Exec model p.body input outcome

end Silmaril.SSA.PEG.Simple
