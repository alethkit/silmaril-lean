module

public import Silmaril.SSA.SeaOfNodes.Pure.SubZero.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Pass.Defs

/-! Find and erase explicit right identities in the current pure word table. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass

open Diamond (Dataflow Ty ValueSort)
open GVN (Producer)
open GVN.Elimination (inFinal)
open SubZero (BinaryOpcode operandsFor? rewriteRightIdentity? word)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- The supported opcode cases of the shared right-identity checker. -/
def opcodes : List BinaryOpcode := [.sub, .add, .mul]

/-- Reuse the typed producer enumeration, retaining only word results. -/
def wordProducers (flow : Dataflow SubZero.Opcode args past sigs) : List (Producer flow word) :=
  (GVN.Pass.candidates flow).filterMap fun
    | ⟨.data (), ref⟩ => some ref
    | ⟨.predicate, _⟩ => none

/-- Resolve the actual second operand by its exact address and delegate the
literal and erasure decision to the shared checker. -/
def rewriteCandidate? (program : Program SubZero.Opcode inputs out)
    (sources : List (Producer program.dataflow word)) (candidate : Producer program.dataflow word)
    (opcode : BinaryOpcode) : Option (Program SubZero.Opcode inputs out) :=
  (operandsFor? opcode candidate).bind fun (_, rhs) =>
    let address := (inFinal candidate rhs).address
    sources.findSome? fun source =>
      if address = source.origin.address then rewriteRightIdentity? opcode program candidate source
      else none

/-- Apply the first accepted identity in current table order. -/
def step? (program : Program SubZero.Opcode inputs out) : Option (Program SubZero.Opcode inputs out) :=
  let producers := wordProducers program.dataflow
  producers.findSome? fun candidate =>
    opcodes.findSome? (rewriteCandidate? program producers candidate)

/-- There is no nomination accepted by the shared checker in this program. -/
def Normal (program : Program SubZero.Opcode inputs out) : Prop :=
  ∀ (opcode : BinaryOpcode) (candidate literal : Producer program.dataflow word),
    rewriteRightIdentity? opcode program candidate literal = none

structure Result (inputs : List (ValueSort Unit)) (out : ValueSort Unit) where
  program : Program SubZero.Opcode inputs out
  deletions : Nat

/-- Spend one unit of fuel per successful step on the current program. -/
def runWith (advance : Program SubZero.Opcode inputs out → Option (Program SubZero.Opcode inputs out)) :
    Nat → Program SubZero.Opcode inputs out → Result inputs out
  | 0, current => ⟨current, 0⟩
  | fuel + 1, current =>
    match advance current with
    | none => ⟨current, 0⟩
    | some next =>
      let final := runWith advance fuel next
      ⟨final.program, final.deletions + 1⟩

/-- Scan the rewritten table at each step for another right identity. -/
def run (fuel : Nat) (program : Program SubZero.Opcode inputs out) : Result inputs out :=
  runWith step? fuel program

/-- Enough fuel for every possible deletion and a final search. -/
def normalize (program : Program SubZero.Opcode inputs out) : Result inputs out :=
  run (program.sigs.length + 1) program

end Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass
