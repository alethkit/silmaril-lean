module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Defs

/-! # A typed header/body loop with two external exits -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit

open Isotope.LambdaSSA (Tm Region)
open OrderedTheta (carried results)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B C D : τ}

structure Blocks (Φ : Type u) [HasTy Φ τ] (A B C D : τ) where
  header : TwoBlock.Instruction Φ A (Silmaril.coprod C B)
  body : TwoBlock.Instruction Φ B (Silmaril.coprod D A)

/-- Locals 0 and 1 carry A and B. External labels 2 and 3 carry C and D. -/
def header (op : Φ) : Region Φ :=
  .case (.op op (.var 0)) (.br 2 (.var 0)) (.br 1 (.var 0))

def body (op : Φ) : Region Φ :=
  .case (.op op (.var 0)) (.br 3 (.var 0)) (.br 0 (.var 0))

def blocks (headOp bodyOp : Φ) : Fin 2 → Region Φ :=
  Fin.cases (header headOp) (fun _ => body bodyOp)

def region (headOp bodyOp : Φ) : Region Φ :=
  .cfg (.br 0 (.var 0)) 2 (blocks headOp bodyOp)

theorem headerTyping (s : Blocks Φ A B C D) :
    Region.HasType [A, A] (header s.header.op) [A, B, C, D] :=
  .case (s.header.typing [A]) (.br rfl (.var rfl)) (.br rfl (.var rfl))

theorem bodyTyping (s : Blocks Φ A B C D) :
    Region.HasType [B, A] (body s.body.op) [A, B, C, D] :=
  .case (s.body.typing [A]) (.br rfl (.var rfl)) (.br rfl (.var rfl))

theorem blockTyping (s : Blocks Φ A B C D) (i : Fin 2) :
    Region.HasType (TwoBlock.localTypes A B i :: [A]) (blocks s.header.op s.body.op i) [A, B, C, D] :=
  Fin.cases (motive := fun j => Region.HasType (TwoBlock.localTypes A B j :: [A])
    (blocks s.header.op s.body.op j) [A, B, C, D])
    (headerTyping s) (fun _ => bodyTyping s) i

theorem regionTyping (s : Blocks Φ A B C D) :
    Region.HasType [A] (region s.header.op s.body.op) [C, D] :=
  .cfg (TwoBlock.localTypes A B) (.br rfl (.var rfl)) (blockTyping s)

/-- The nested θ interface has one common type for entry, feedback and
return. The right summand carries the active header input. -/
abbrev ExitCode (C D : τ) := Silmaril.coprod C D
abbrev Carrier (A C D : τ) := Silmaril.coprod (ExitCode C D) A
abbrev Route (B C D : τ) := Silmaril.coprod (ExitCode C D) B

abbrev headerPorts (B C D : τ) : Ports (OrderedRuntime.Structured.Ty τ) :=
  [.control 2, .value (Route B C D)]
abbrev armPorts (A B C D : τ) : Ports (OrderedRuntime.Structured.Ty τ) :=
  [.value (Carrier A C D), .value (Route B C D)]

inductive Pure (τ : Type u) [TypeFormers τ] : Dialect.{u,u} τ PUnit where
  | exit {A B C D : τ} : Pure τ (armPorts A B C D) (results (Carrier A C D))

inductive Effect (Φ : Type u) [HasTy Φ τ] : Dialect.{u,u} τ PUnit where
  | header {A B C D : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod C B) →
      Effect Φ (carried (Carrier A C D)) (headerPorts B C D)
  | body {A B C D : τ} : TwoBlock.Instruction Φ B (Silmaril.coprod D A) →
      Effect Φ (armPorts A B C D) (results (Carrier A C D))

abbrev Op (Φ : Type u) [HasTy Φ τ] := OrderedRuntime.Structured.Instruction (Pure τ) (Effect Φ)

def arm (op : Op Φ (armPorts A B C D) (results (Carrier A C D))) :
    NestedTheta.Term (Op Φ) (armPorts A B C D) [] [results (Carrier A C D)] (results (Carrier A C D)) :=
  .bind ⟨_, .base (.simple op), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    fun i => i.elim0⟩
    (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

def thetaBody (s : Blocks Φ A B C D) : NestedTheta.Term (Op Φ) (carried (Carrier A C D)) []
    [headerPorts B C D, results (Carrier A C D)] (results (Carrier A C D)) :=
  let headerNode : NestedTheta.Node (Op Φ) (carried (Carrier A C D)) [] (headerPorts B C D) :=
    ⟨_, .base (.simple (.effect (.header s.header))), .cons (.arg .head) .nil, fun i => i.elim0⟩
  let selectNode : NestedTheta.Node (Op Φ) (carried (Carrier A C D)) [headerPorts B C D]
      (results (Carrier A C D)) :=
    ⟨.control 2 :: armPorts A B C D, .base (.gamma 0),
      .cons (.output (0 : Fin 1) .head)
        (.cons (.arg .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)),
      fun _ => [results (Carrier A C D)]⟩
  .bind headerNode (fun i => i.elim0) <|
    .bind selectNode (Fin.cases (arm (.pure Pure.exit)) (fun _ => arm (.effect (.body s.body)))) <|
      .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))

abbrev Loop (Φ : Type u) [HasTy Φ τ] (A C D : τ) :=
  NestedTheta.Graph (Op Φ) (carried (Carrier A C D)) [] [carried (Carrier A C D)]
    (carried (Carrier A C D))

def loopTerm (s : Blocks Φ A B C D) : NestedTheta.Term (Op Φ) (carried (Carrier A C D)) []
    [carried (Carrier A C D)] (carried (Carrier A C D)) :=
  .bind (NestedTheta.thetaVertex [headerPorts B C D, results (Carrier A C D)])
    (fun _ => thetaBody s) (.ret (NestedTheta.thetaResults (carried (Carrier A C D))))

def graph (s : Blocks Φ A B C D) : Loop Φ A C D := (loopTerm s).toGraph

inductive SSAForm (A B C D : τ) : Region Φ → Type u where
  | loop (s : Blocks Φ A B C D) : SSAForm A B C D (region s.header.op s.body.op)

inductive RVForm (A B C D : τ) : Loop Φ A C D → Type u where
  | loop (s : Blocks Φ A B C D) : RVForm A B C D (graph s)

/-- Both forms use the same typed block instructions and fixed wiring. -/
inductive Related (A B C D : τ) : Region Φ → Loop Φ A C D → Type u where
  | loop (s : Blocks Φ A B C D) : Related A B C D (region s.header.op s.body.op) (graph s)

def lower {r : Region Φ} (h : SSAForm A B C D r) : Σ g : Loop Φ A C D, Related A B C D r g :=
  match h with
  | .loop s => ⟨graph s, .loop s⟩

def raise {g : Loop Φ A C D} (h : RVForm A B C D g) : Σ r : Region Φ, Related A B C D r g :=
  match h with
  | .loop s => ⟨region s.header.op s.body.op, .loop s⟩

def Related.instructions {r : Region Φ} {g : Loop Φ A C D} (h : Related A B C D r g) : Blocks Φ A B C D :=
  match h with
  | .loop s => s

theorem Related.typing {r : Region Φ} {g : Loop Φ A C D} (h : Related A B C D r g) :
    Region.HasType [A] r [C,D] := by
  cases h with
  | loop s => exact regionTyping s

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit
