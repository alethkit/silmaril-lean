module

public import Silmaril.Semantics.Page.Trace.Labelled.Defs
import Silmaril.Proofs.Semantics.Page.Trace.Labelled

public section
namespace Silmaril.Semantics.Page

universe u v w
variable {Id : Type u} {Content : Type v} {Memory : Type w}
variable {access : Access Id Content Memory} {trace : Trace Id Content} {initial final : Memory}

theorem Trace.replays_iff_path :
    trace.Replays access initial final ↔ access.labelled.Path initial trace final :=
  Proofs.Semantics.Page.replays_iff_path

theorem Trace.consistent_iff_finishes :
    trace.Consistent access initial ↔ access.labelled.Finishes initial trace (.returned ()) := by
  simp only [Trace.Consistent, Operational.Labelled.Finishes, Access.labelled, and_true,
    Trace.replays_iff_path]

end Silmaril.Semantics.Page
