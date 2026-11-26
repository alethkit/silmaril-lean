module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Defs

/-! # Post-join forwarding across disjoint Stores -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint

open RVSDG (Port Tuple)
open SeaOfNodes.Diamond (Slot)

variable {args : List ValueSort} {cells : Nat}

/-- One incoming occurrence's nominated Store and the arguments that
certify disjoint writes after that Store. -/
structure ArmCertificate (args : List ValueSort) where
  storeVersion : Nat
  writers : List (Port args .address)

structure Candidate (args : List ValueSort) where
  first : ArmCertificate args
  second : ArmCertificate args

def Candidate.atSlot (candidate : Candidate args) : Slot → ArmCertificate args
  | .first => candidate.first
  | .second => candidate.second

/-- The initial suffix Load determines the one observed address argument.
Each certificate supplies its own intervening writers. -/
def ArmCertificate.atAddress (arm : ArmCertificate args) (address : Port args .address) :
    Memory.Forwarding.Disjoint.Certificate args :=
  ⟨address, arm.writers⟩

def checkSlot (graph : Graph args) (address : Port args .address) (candidate : Candidate args)
    (input : Tuple (Val cells) args) (arrival : Slot) : Bool :=
  let arm := candidate.atSlot arrival
  let certificate := arm.atAddress address
  certificate.check input &&
    Memory.Forwarding.Disjoint.checkExitWith (graph.arm (graph.merge.predecessor arrival))
      arm.storeVersion certificate

def checkJoined (graph : Graph args) (address : Port args .address) (candidate : Candidate args)
    (input : Tuple (Val cells) args) : Bool :=
  checkSlot graph address candidate input .first && checkSlot graph address candidate input .second

/-- Remove the head Load of the shared suffix after validating both
occurrences' facts on the concrete input. -/
def rewrite (graph : Graph args) (candidate : Candidate args) (input : Tuple (Val cells) args) :
    Option (Graph args) :=
  Memory.Diamond.Forwarding.rewriteUsing graph (fun address => checkJoined graph address candidate input)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint
