module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Defs

/-! # Normalize serial continuations before numbered emission -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization

open Reverse (Normal)
open Sequential.Flat.Serial (Joined payloadData)
open NestedTheta.ExplicitRuntime (EntryChecked)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z H M I J L E D : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- A typed serial suffix goes after the last loop on the continuation
path. For a fork that path starts at its existing shared continuation. -/
def append : {A X Z H : τ} → {ps : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Normal Φ A X Z H M M ps → Normal Φ M I J L E D qs →
    Normal Φ A X Z L E D (Joined M I J ps qs)
  | _, _, _, _, _, .loop first, tail => .link first tail
  | _, _, _, _, _, .link first rest, tail => .link first (append rest tail)
  | _, _, _, _, _, .branch gate left right rest, tail => .branch gate left right (append rest tail)

/-- Every structured source has an outer normal form with the same typed
boundary and ordered vertex signature table. -/
def normalize : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Syntax Φ A X Z L E D sigs → Normal Φ A X Z L E D sigs
  | _, _, _, _, _, _, _, .loop s => .loop s
  | _, _, _, _, _, _, _, .link p q => append (normalize p) (normalize q)
  | _, _, _, _, _, _, _, .branch gate left right tail =>
    .branch gate (normalize left) (normalize right) (normalize tail)

/-- Emit the normal layout recognized by the structured reverse compiler. -/
def compile (s : Syntax Φ A X Z L E D sigs) : Sequential.Flat.Serial.Graph Φ A X Z L E D sigs :=
  (normalize s).toSyntax.graph

def compileChecked (s : Syntax Φ A X Z L E D sigs) :
    EntryChecked (a := payloadData A X Z) (b := payloadData L E D) (compile s).toTerm :=
  (Related.generated (normalize s).toSyntax).checked

/-- Compare the old and normal emissions at their common typed signature,
including all numbered input and result wires and child tables. -/
def decideNumbering [DecidableEq τ] [DecidableEq Φ] (s : Syntax Φ A X Z L E D sigs) :
    Decidable (s.graph = compile s) :=
  NestedTheta.Equality.decideGraph (Sequential.Flat.Numbered.Recognize.opcodeCode (τ := τ) (Φ := Φ))
    s.graph (compile s)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization
