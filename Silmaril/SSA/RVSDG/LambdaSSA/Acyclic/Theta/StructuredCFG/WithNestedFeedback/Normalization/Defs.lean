module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Defs

/-! # Emit the canonical numbered layout from a mixed structured source -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization

open Reverse.Recursive (Normal)
open Sequential.Flat.Serial (Joined payloadData)
open NestedTheta.ExplicitRuntime (EntryChecked)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z H M I J L E D : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- Embed the ordinary normalizer’s output in the mixed grammar. -/
def ofStructured : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    StructuredCFG.Reverse.Normal Φ A X Z L E D sigs → Normal Φ A X Z L E D sigs
  | _, _, _, _, _, _, _, .loop s => .leaf (.localLoop s)
  | _, _, _, _, _, _, _, .link s k => .seq (.localLoop s) (ofStructured k)
  | _, _, _, _, _, _, _, .branch gate p q k =>
    .fork gate (ofStructured p) (ofStructured q) (ofStructured k)

/-- Keep both arms of a fork in place and append the suffix along its shared
continuation. Either kind of loop is a leaf of this outer recursion. -/
def append : {A X Z H : τ} → {ps : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Normal Φ A X Z H M M ps → Normal Φ M I J L E D qs →
    Normal Φ A X Z L E D (Joined M I J ps qs)
  | _, _, _, _, _, .leaf p, tail => .seq p tail
  | _, _, _, _, _, .seq (.localLoop p) k, tail => .seq (.localLoop p) (append k tail)
  | _, _, _, _, _, .seq (.feedback p) k, tail => .seq (.feedback p) (append k tail)
  | _, _, _, _, _, .fork gate p q k, tail => .fork gate p q (append k tail)

/-- Normalize the outer serial and fork structure while preserving the
typed boundary and signature table. Each nested-feedback leaf stays intact. -/
def normalize : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Syntax Φ A X Z L E D sigs → Normal Φ A X Z L E D sigs
  | _, _, _, _, _, _, _, .structured s => ofStructured (StructuredCFG.Normalization.normalize s)
  | _, _, _, _, _, _, _, .nested s => .leaf (.feedback s)
  | _, _, _, _, _, _, _, .link p q => append (normalize p) (normalize q)
  | _, _, _, _, _, _, _, .branch gate p q k => .fork gate (normalize p) (normalize q) (normalize k)

def compile (s : Syntax Φ A X Z L E D sigs) : Sequential.Flat.Serial.Graph Φ A X Z L E D sigs :=
  (normalize s).toSyntax.graph

def compileChecked (s : Syntax Φ A X Z L E D sigs) :
    EntryChecked (a := payloadData A X Z) (b := payloadData L E D) (compile s).toTerm :=
  (Related.generated (normalize s).toSyntax).checked

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization
