module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected

open LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement (ReadTree)

private abbrev tail : List Sorts := [Bit]
private def first : Position (Bit :: tail) := ⟨0, rfl⟩
private def second : Position (Bit :: tail) := ⟨1, rfl⟩

private def fixture (bound : Bool) (result : Expr 2) (target : Position (Bit :: tail)) :
    ReadTree (Bit :: tail) 0 :=
  .request [false] true bound
    (.request [] false bound (.retExpr [] first (.literal false))
      (.testRequest [false] 1 false bound bound
        (.retExpr [true] first result) (.ret [] first 0)
        (.retExpr [true] target result) (.ret [] second 0)))
    (.ret [] second 0)

private def before := fixture true (.read 1) second
private def table := fixture false (Expr.quote 2 (fun env => env 1)) second
private def differentExit := fixture true (.read 1) first

-- The outer bit still selects the third request. The terminal reads
-- the other retained bit directly or through an explicit native table.
private theorem sameArrow : denotation before = denotation table := by
  apply (denotation_eq_iff_normal Bit tail _ _).mpr
  have tableEntry : (Expr.quote 2 (fun env => env 1)).eval = (Expr.read (1 : Fin 2)).eval :=
    funext (Expr.quote_eval 2 (fun env => env 1))
  simp only [before, table, fixture, witnessed, Source.normal, ReadTree.witnessed,
    List.foldr_cons, List.foldr_nil, Tree.normal, tableEntry]

example : Derivable false (equation Bit tail before table) :=
  (denotation_eq_iff_derivable Bit tail _ _).mp sameArrow

-- Fix both prior replies and the last reply. Changing the outward
-- position alone separates the packed arrows for the same output type.
example : denotation before ≠ denotation differentExit := by
  intro same
  have normal := (denotation_eq_iff_normal Bit tail _ _).mp same
  have selected := (Path.emit.inj normal).2
  have outer := (Path.request.inj selected).2.2.1
  have inner := (Path.request.inj outer).2.2.2.2
  have guard := (Path.emit.inj inner).2
  have reply := (Path.request.inj guard).2.1
  have pos := (Path.ret.inj (Path.emit.inj reply).2).1
  have atSlot := congrArg (fun p : Position (Bit :: tail) => p.1.val) pos
  contradiction

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected
