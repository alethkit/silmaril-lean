module

public import Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Defs

/-! Level-checked lowering for the TLA+ collection fragment. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Collections

open Resolution

/-- Select a closed constant- or state-level definition in the checked registry.
In addition to the core data forms, admit single-identifier bounded functions,
records, function sets and sets of records. The result requires a collection
adapter for evaluation. -/
public def lowerState (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) (maxDepth : Nat) (id : BindingId) :
    Except Endpoints.Diagnostic (CheckedExpr signature .collections) :=
  Endpoints.lowerStateIn registry externalLevels signature .collections maxDepth id

end Silmaril.Logic.Temporal.TLA.DataElab.Collections
