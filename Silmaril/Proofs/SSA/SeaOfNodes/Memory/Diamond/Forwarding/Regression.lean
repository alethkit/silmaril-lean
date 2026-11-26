module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding

open RVSDG (Tuple Origin)
open SeaOfNodes.Diamond (Projection)

private abbrev args : List ValueSort := [.address, .address, .address, .word]

private def xWire {past : List (List ValueSort)} : Origin args past .address := .arg .head
private def yWire {past : List (List ValueSort)} : Origin args past .address := .arg (.tail .head)
private def zWire {past : List (List ValueSort)} : Origin args past .address := .arg (.tail (.tail .head))
private def immediate {past : List (List ValueSort)} : Origin args past .word :=
  .arg (.tail (.tail (.tail .head)))

private def exportLoaded (version : Nat) : Memory.Body args [[.word]] version :=
  .load (.latest version) zWire (.ret (.latest version) (.output (1 : Fin 2) .head))

-- The true arm stores a local Load result and exports it across another Load.
private def trueArm (clobber : Bool) : Memory.Graph args :=
  let loaded : Origin args [[.word]] .word := .output (0 : Fin 1) .head
  .load (.latest 0) yWire
    (.store (.latest 0) zWire loaded
      (.store (.latest 1) xWire loaded
        (if clobber then .store (.latest 2) xWire immediate (exportLoaded 3) else exportLoaded 2)))

private def falseArm (hasStore : Bool) : Memory.Graph args :=
  if hasStore then .store (.latest 0) xWire immediate (.ret (.latest 1) immediate)
  else .ret (.latest 0) immediate

-- The shared Load feeds both a later Store and Return across an observing read.
private def postJoin : Memory.Graph (.word :: args) :=
  .load (.latest 0) (.arg (.tail .head))
    (.store (.latest 0) (.arg (.tail (.tail (.tail .head)))) (.output (0 : Fin 1) .head)
      (.load (.latest 1) (.arg (.tail (.tail .head)))
        (.ret (.latest 1) (.output (1 : Fin 2) .head))))

private def forwarded : Memory.Graph (.word :: args) :=
  .store (.latest 0) (.arg (.tail (.tail (.tail .head)))) (.arg .head)
    (.load (.latest 1) (.arg (.tail (.tail .head))) (.ret (.latest 1) (.arg .head)))

private def source (first : Projection) (clobber : Bool := false) (hasStore : Bool := true) :
    Graph args where
  merge := ⟨first⟩
  arm
    | .onTrue => trueArm clobber
    | .onFalse => falseArm hasStore
  suffix := postJoin

private def target (first : Projection) : Graph args :=
  { source first with suffix := forwarded }

private theorem acceptedNormal : rewrite (source .onTrue) ⟨2, 1⟩ = some (target .onTrue) := rfl
private theorem acceptedReverse : rewrite (source .onFalse) ⟨1, 2⟩ = some (target .onFalse) := rfl

-- Entries of a candidate name Region positions, including in reversed order.
example : rewrite (source .onFalse) ⟨2, 1⟩ = none := rfl

-- True overwrites the observed address after version 2. Updating the
-- candidate to version 3 still fails because the arm exports the old word.
example : rewrite (source .onTrue (clobber := true)) ⟨2, 1⟩ = none := rfl
example : rewrite (source .onTrue (clobber := true)) ⟨3, 1⟩ = none := rfl

-- The false arm has no Store. True's independent evidence cannot stand in for it.
example : rewrite (source .onTrue (hasStore := false)) ⟨2, 1⟩ = none := rfl
example : rewrite (source .onFalse (hasStore := false)) ⟨1, 2⟩ = none := rfl

private def x : Address 3 := 0
private def y : Address 3 := 1
private def z : Address 3 := 2
private def initial : Heap 3 := fun address => if address = y then 11 else 0
private def input : Tuple (Val 3) args := .cons x (.cons y (.cons z (.cons (33 : Word) .nil)))
private def finalTrue : Heap 3 := ((initial.write z 11).write x 11).write z 11
private def finalFalse : Heap 3 := (initial.write x 33).write z 33

example : (target .onTrue).Returns true input initial 11 finalTrue :=
  (rewrite_returns_iff acceptedNormal true input initial 11 finalTrue).mpr
    (((source .onTrue).returns_iff_denote true input initial 11 finalTrue).mpr (by cbv))

example : (target .onFalse).Returns false input initial 33 finalFalse :=
  (rewrite_returns_iff acceptedReverse false input initial 33 finalFalse).mpr
    (((source .onFalse).returns_iff_denote false input initial 33 finalFalse).mpr (by cbv))

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding
