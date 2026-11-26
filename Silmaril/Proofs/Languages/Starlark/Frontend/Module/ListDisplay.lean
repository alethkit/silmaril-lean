module

public import Silmaril.Languages.Starlark.Functions.Expressions.Denotation.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Frontend.Module

open Silmaril.Languages.Starlark
open Functions Functions.Lowering

theorem denoteList_order (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (elements : List Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.list elements) state =
      match (elements.mapM (denoteExprWith program available bodyMeaning)) state with
      | .ok values next => Lists.allocate values next
      | .error error next => .error error next := by
  rw [denoteExprWith.eq_2]
  rw [List.mapM_subtype (g := denoteExprWith program available bodyMeaning) (fun _ _ => rfl), List.unattach_attach]
  simp only [Lists.Outcome.resume]
  cases (elements.mapM (denoteExprWith program available bodyMeaning)) state <;> rfl

theorem denoteList_cons (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (first : Expr) (rest : List Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.list (first :: rest)) state =
      match denoteExprWith program available bodyMeaning first state with
      | .ok value next =>
        match (rest.mapM (denoteExprWith program available bodyMeaning)) next with
        | .ok values after => Lists.allocate (value :: values) after
        | .error error after => .error error after
      | .error error next => .error error next := by
  rw [denoteList_order, List.mapM_cons]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  cases denoteExprWith program available bodyMeaning first state with
  | error _ _ => rfl
  | ok _ next =>
    dsimp only
    cases (rest.mapM (denoteExprWith program available bodyMeaning)) next <;> rfl

end Silmaril.Proofs.Languages.Starlark.Frontend.Module
