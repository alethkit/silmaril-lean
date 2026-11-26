module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Correctness

/-! # Transfer agreement and exact finite returns for one cyclic quad loop -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop

open RVSDG (Tuple Wires Locals)
open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

universe u v w
variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out test : ValueSort Data}
variable {args : List (Ty Data)} {past : List (List (Ty Data))}

/-- Reading the constructed outgoing column gives the ordered source's final register bank. -/
theorem compile_agrees (code : Code Op regs test) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (compile code current).outgoing.read entry ((compile code current).flow.eval m entry locals) =
      finalBank m code (current.read entry locals) :=
  Proofs.compile_agrees code m entry locals current

/-- The provisional header arguments read the bank delivered by the taken incoming edge. -/
theorem header_read (m : Model.{u, v, w} Op)
    (input old : Tuple (Val m.value) (dataPorts regs)) :
    (headerVersions regs).read (appendTuple old input) PUnit.unit = old :=
  Proofs.header_read m input old

/-- The entry column supplies the initialized register bank. -/
theorem Program.lower_initial (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (input : Tuple (Val m.value) (dataPorts regs)) :
    p.lower.initial m input = input :=
  Proofs.lower_initial p m input

/-- One activation agrees on the exit result or the entire bank sent on the backedge. -/
theorem Program.lower_step (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (input old : Tuple (Val m.value) (dataPorts regs)) :
    p.lower.step m input old = p.step m old :=
  Proofs.lower_step p m input old

/-- Lowering preserves and reflects finite returns with the exact completed backedge count. -/
theorem Program.lower_returnsAfter_iff (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (input old : Tuple (Val m.value) (dataPorts regs)) (count : Nat) (result : sortValue m.value out) :
    p.lower.ReturnsAfter m input count old result ↔ p.ReturnsAfter m count old result :=
  Proofs.lower_returnsAfter_iff p m input old count result

/-- Lowering preserves and reflects every finite return from the initialized bank. -/
theorem Program.lower_returns_iff (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (input : Tuple (Val m.value) (dataPorts regs)) (result : sortValue m.value out) :
    p.lower.Returns m input result ↔ p.Returns m input result :=
  Proofs.lower_returns_iff p m input result

/-- Source and graph evaluators agree at every backedge budget. -/
theorem Program.lower_evalBackedges (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (budget : Nat) (input : Tuple (Val m.value) (dataPorts regs)) :
    p.lower.evalBackedges m budget input = p.evalBackedges m budget input :=
  Proofs.lower_evalBackedges p m budget input

end Silmaril.SSA.SeaOfNodes.Quads.Loop
