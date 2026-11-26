module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs

/-! Typed linker sources used to check direct captured calls. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct

open Isomorphism.Local.Gamma (extendOrigin)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)}

def capturePort {Ty : Type u} {params : Ports Ty} {ty : Ty} :
    (context : Ports Ty) → Port (context ++ params) ty → Option (Port context ty)
  | [], _ => none
  | _ :: _, .head => some .head
  | _ :: rest, .tail p => (capturePort rest p).map Port.tail

/-- Compose capture edges with the actual linker wires. Formals and
outputs of local bindings have no direct source in the captures. -/
def project {Ty : Type u} {imports context params : Ports Ty} {past localSigs : List (Ports Ty)}
    (wires : Wires imports past context) : {users : Ports Ty} →
      Wires (context ++ params) localSigs users → Option (Wires imports past users)
  | _, .nil => some .nil
  | _, .cons (.arg p) rest => do
    let captured ← capturePort context p
    let tail ← project wires rest
    pure (.cons (wires.get captured) tail)
  | _, .cons (.output _ _) _ => none

def widen {args users head : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (wires : Wires args past users) : Wires args (past ++ [head]) users :=
  wires.map fun _ origin => extendOrigin origin head

def phiCaptures (family : StaticDemand.Family Op table imports) (i : Fin table.members.length) :
    Option (Wires imports [memberPorts table.members] (table.at i).captures) :=
  project (widen family.captures) (StaticDemand.Family.dropPrefix (memberPorts table.members) (family.memberWires i))

/-- The target and its capture witnesses, taken together in call order. -/
abbrev CallPorts (table : MemberSummaries V S) (i : Fin table.members.length) :=
  (table.at i).fn.port :: (table.at i).captures

def seedWires (i : Fin table.members.length)
    (captures : Wires imports [memberPorts table.members] (table.at i).captures) :
    Wires imports [memberPorts table.members] (CallPorts table i) :=
  .cons (.output (0 : Fin 1) (memberPort table.members i)) captures

def newWires {scope : Scope m} {fn : Function V S} (binding : Binding Op scope.table imports scope.past fn) :
    Wires imports (scope.past ++ [[fn.port]])
      (CallPorts (prepend binding.summary scope.table) (0 : Fin (scope.table.members.length + 1))) :=
  .cons ((lastExport scope.past fn : Wires imports _ [fn.port]).get .head) (widen binding.captures)

def selects (guard : Guard m table) (i : Fin table.members.length)
    (values : Tuple m.Val (CallPorts table i)) : Prop :=
  guard i (values.get .head) (StaticDemand.Family.dropPrefix [(table.at i).fn.port] values)

/-- Source wires for one checked slot, with resolution evidence for their
actual values on both sides of the linker. -/
structure Route (inputsL inputsR : Tuple m.Val imports) (scope : Scope m)
    (i : Fin scope.table.members.length) where
  wires : Wires imports scope.past (CallPorts scope.table i)
  left : selects scope.guardL i (wires.read inputsL scope.localsL)
  right : selects scope.guardR i (wires.read inputsR scope.localsR)

/-- Slots remain usable by explicit resolution even when there is no
direct-source description of their captures. -/
abbrev Routes (inputsL inputsR : Tuple m.Val imports) (scope : Scope m) :=
  (i : Fin scope.table.members.length) → Option (Route inputsL inputsR scope i)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct
