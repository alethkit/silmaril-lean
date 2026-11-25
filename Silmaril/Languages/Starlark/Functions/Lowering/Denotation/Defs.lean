module

public import Silmaril.Languages.Starlark.Functions.Denotation.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

abbrev coreClosureMeaning (program : Program) (available : List DeclarationId) : ClosureMeaning available :=
  fun plan => denoteBody program (withoutDeclaration available plan.id) plan.body

abbrev denoteDispatch (program : Program) (available : List DeclarationId) :=
  denoteDispatchWith program available (coreClosureMeaning program available)

abbrev denoteApplication (program : Program) (available : List DeclarationId) :=
  denoteApplicationWith program available (coreClosureMeaning program available)

/-- Direct state-and-error denotation using the finite declaration core. -/
abbrev denoteExpr (program : Program) (available : List DeclarationId) :=
  denoteExprWith program available (coreClosureMeaning program available)

end Silmaril.Languages.Starlark.Functions.Lowering
