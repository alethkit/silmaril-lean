module

import Silmaril.Formats.Dasl.Prolly.Range.Thms
public meta import Silmaril.Formats.Dasl.Prolly.Range.Defs

namespace Silmaril.Formats.Dasl.Prolly.Range.Examples

open Silmaril.Semantics.Prolly (Block)

private def fixture (complete : Bool) : Nat → Except (Fault Nat) (Block Nat Nat String)
  | 1 => .ok (.branch 1 [(2, 2), (4, 3), (6, 4)])
  | 2 => if complete then .ok (.leaf [(1, "one"), (2, "two")]) else .error (.missing 2)
  | 3 => .ok (.leaf [(3, "three"), (4, "four")])
  | 4 => .ok (.leaf [(5, "five"), (6, "six")])
  | _ => .error (.invalidWire 5)

#guard scan (fixture true) 4 1 7 2 none 1 =
  .ok ⟨[(1, "one"), (2, "two"), (3, "three"), (4, "four"), (5, "five"), (6, "six")], 4⟩
#guard scan (fixture false) 4 3 5 2 none 1 = .ok ⟨[(3, "three"), (4, "four")], 3⟩
#guard scan (fixture false) 4 3 3 2 none 1 = .ok ⟨[], 3⟩
#guard scan (fixture false) 4 2 5 2 none 1 = .error (.missing 2)
#guard scan (fixture false) 4 3 5 1 none 1 = .error (.fuel 3)
#guard scan (fixture false) 4 3 5 2 none 5 = .error (.invalidWire 5)
#guard scan (fixture false) 2 3 5 2 none 1 = .error (.invalidNode 1)

end Silmaril.Formats.Dasl.Prolly.Range.Examples
