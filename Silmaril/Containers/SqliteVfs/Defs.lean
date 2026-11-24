module

public import Silmaril.Containers.Machine.Defs
public import Silmaril.Machine.SqliteVfs.Defs

@[expose] public section

namespace Silmaril.Containers.SqliteVfs

open Silmaril.Machine.SqliteVfs

/-- Logical call and return events at the container machine boundary. Each
return carries the request index needed to type its response. -/
inductive Event where
  | recv (request : Request)
  | send (exchange : Exchange)

/-- Every completed exchange contributes one receive and one send, in order. -/
def encode (trace : Trace) : List Event :=
  trace.flatMap fun exchange => [.recv exchange.request, .send exchange]

/-- Serial request service. There is at most one pending request. -/
inductive Phase (State : Type) where
  | idle (state : State)
  | pending (state : State) (request : Request)

inductive Step {State : Type} (handler : Handler State) :
    Phase State → Mach.Act Event → Phase State → Prop where
  | recv (state : State) (request : Request) :
      Step handler (.idle state) (.ev (.recv request)) (.pending state request)
  | send {before after : State} {request : Request} {response : Response request} :
      handler before request = (response, after) →
      Step handler (.pending before request) (.ev (.send ⟨request, response⟩)) (.idle after)

/-- An instance of the landed container machine interface, with no internal
actions. A receive is an input and a send is an output. -/
def machine {State : Type} (handler : Handler State) : Mach.MachineSem State Event where
  State := Phase State
  isIn
    | .recv _ => true
    | .send _ => false
  load initial phase := phase = .idle initial
  step := Step handler
  final _ _ := False

/-- The abstract container loader supplies an initial handler state. Runtime
observations retain the machine's events and its blocking behavior. -/
def runtime {State : Type} (handler : Handler State) : Runtime State State Event :=
  Runtime.ofMachine Except.ok (machine handler)

end Silmaril.Containers.SqliteVfs
