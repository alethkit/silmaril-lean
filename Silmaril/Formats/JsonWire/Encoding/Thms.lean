module

public import Silmaril.Formats.JsonWire.Defs
import Silmaril.Proofs.Formats.JsonWire.Encoding

@[expose] public section

namespace Silmaril.Formats.JsonWire

/-- Reading the printer's actual bytes recovers every ordered RFC JSON tree,
including exact decimal fields, all UTF-16 units, and duplicate names. -/
theorem parse_encode (tree : Ast Decimal) : parse? (encode tree) = some tree :=
  Silmaril.Proofs.Formats.JsonWire.Encoding.parse_encode tree

end Silmaril.Formats.JsonWire
