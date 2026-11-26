module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs

/-! # Sink one pure total let into its sole consuming λSSA arm -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Sink

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Φ : Type u} {τ : Type v}

def forward : Region Φ := .br 2 (.var 0)

/-- Entry arguments in de Bruijn order are the tag, the operand and the
independent right-arm result. The fresh result is used only on edge zero. -/
def before (op : Φ) : Region Φ :=
  .cfg (.let₁ (.op op (.var 1)) (.case (.var 1) (.br 0 (.var 1)) (.br 1 (.var 4))))
    2 (fun _ => forward)

/-- Send the operand down edge zero and compute the result in block zero.
Edge one and its block still forward the independent right-arm value. -/
def after (op : Φ) : Region Φ :=
  .cfg (.case (.var 0) (.br 0 (.var 2)) (.br 1 (.var 3))) 2
    (Fin.cases (.let₁ (.op op (.var 0)) forward) (fun _ => forward))

/-- Admission fixes the entire use footprint, including both block bodies. -/
inductive Admitted : Region Φ → Type u where
  | entryLet (op : Φ) : Admitted (before op)

def Admitted.opcode {r : Region Φ} : Admitted r → Φ
  | .entryLet op => op

def admit : (r : Region Φ) → Option (Admitted r)
  | .cfg (.let₁ (.op op (.var 1)) (.case (.var 1) (.br 0 (.var 1)) (.br 1 (.var 4)))) 2 blocks =>
    match first : blocks 0, second : blocks 1 with
    | .br 2 (.var 0), .br 2 (.var 0) =>
      have same : blocks = fun _ => forward := funext (fun i =>
        Fin.cases (motive := fun j => blocks j = forward) first
          (fun j => Fin.cases (motive := fun k => blocks k.succ = forward)
            second (fun impossible => impossible.elim0) j) i)
      some (same.symm ▸ Admitted.entryLet op)
    | _, _ => none
  | _ => none

/-- Executable rewrite on the admitted shape. The semantic contract interprets
the moved opcode as a pure total function. -/
def sink? (r : Region Φ) : Option (Region Φ) :=
  (admit r).map fun form => after form.opcode

variable [TypeFormers τ] [HasTy Φ τ]

/-- The selector is a sum of units. Both arms return the opcode's result type. -/
def inputs (op : Φ) : List τ := [coprod unit unit, instrSrc op, instrTrg op]

variable {α : Type w} {σ : Type x}

/-- A pure total instruction interpretation for this slice. -/
def instruction (compute : Φ → Value α → Value α)
    (op : Φ) (arg : Value α) (start : σ) (result : Value α) (finish : σ) : Prop :=
  result = compute op arg ∧ finish = start

/-- Both syntaxes have this return payload. Non-sum tags have no finite return. -/
def result? (compute : Φ → Value α → Value α) (op : Φ) (env : Env α) : Option (Value α) :=
  match env 0 with
  | .inl _ => some (compute op (env 1))
  | .inr _ => some (env 2)
  | _ => none

end Silmaril.SSA.SeaOfNodes.GCM.Sink
