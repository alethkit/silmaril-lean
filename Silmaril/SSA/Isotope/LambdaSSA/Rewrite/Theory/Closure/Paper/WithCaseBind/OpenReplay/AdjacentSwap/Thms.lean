module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.AdjacentSwap.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AdjacentTableSwap

/-! # Native interchange of the two structural packet tests -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance adjacentSwapThmsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Reversing the two projection tests and reindexing the truth table gives
the same actual selected terminal. Native product and case expansion apply
to the structural packet, and the common emit prefix stays before the tests. -/
theorem selected_adjacent_swap {L : List (Ty Empty)} (pos : Position L) (bits : List Bool)
    (table : Finite.Table 2) :
    selectedEq (selectTerminal pos (Finite.Expr.quote 2 table) (readReply 2) bits)
      (selectTerminal pos (Finite.Expr.quote 2 (fun row => table (row ∘ Fin.rev)))
        (readReply 2 ∘ Fin.rev) bits) :=
  AdjacentSwap.selected_adjacent_swap pos bits table

/-- The two orders give equal packed arrows from the same open two-reply
product to the same tagged exit interface. -/
theorem packed_adjacent_swap {L : List (Ty Empty)} (pos : Position L) (bits : List Bool)
    (table : Finite.Table 2) :
    packed (.retExpr bits pos (Finite.Expr.quote 2 table)) =
      packedTable pos bits (fun row => table (row ∘ Fin.rev)) Fin.rev :=
  AdjacentSwap.packed_adjacent_swap pos bits table

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
