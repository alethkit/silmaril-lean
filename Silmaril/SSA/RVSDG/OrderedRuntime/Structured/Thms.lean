module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Defs
public import Silmaril.SSA.RVSDG.Thms
import Silmaril.Proofs.SSA.RVSDG.OrderedRuntime.Structured.Adequacy

/-! # Term/graph correspondence and deterministic state adequacy -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured

universe u v w
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

/-- Numbering preserves the admission witness for an inductive region. -/
def Checked.collect {a : Data args} {b : Data outs}
    {t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)}
    (checked : EntryChecked a b t) : EntryChecked a b t.toGraph.toTerm :=
  (Term.toTerm_toGraph t).symm ▸ checked

/-- Collecting the term has no effect on the computation denoted by it. -/
theorem denote_toGraph {M : Type (max u w) → Type (max u w)} [Monad M] (m : Model P E M)
    {a : Data args} {b : Data outs} {t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)}
    (checked : EntryChecked a b t) :
    denoteGraph m t.toGraph checked.collect = checked.denote m :=
  Proofs.denote_transport m (Term.toTerm_toGraph t) checked

theorem encode_decode {ρ : Type (max u w)} {value : V → Type (max u w)}
    (pair : Tuple (Values value) outs × ρ) : encode (decode pair) = pair :=
  Proofs.encode_decode pair

theorem decode_encode {ρ : Type (max u w)} {value : V → Type (max u w)}
    (data : Data outs) (input : Tuple (RuntimeValues value ρ) (Threaded outs)) :
    decode (encode input) = input :=
  Proofs.decode_encode data input

section WireLemmas

variable {F : Ty V → Type w} {ρ : Type (max u w)} {value : V → Type (max u w)}

theorem get_runtime (rt : F runtime) (xs : Tuple F outs) :
    (withRuntime rt xs).get (runtimePort outs) = rt :=
  Proofs.get_runtime rt xs

theorem split_append (rt : F runtime) (xs : Tuple F outs) :
    splitRuntime outs (withRuntime rt xs) = (xs, rt) :=
  Proofs.split_append rt xs

theorem append_split (xs : Tuple F (Threaded outs)) :
    withRuntime (splitRuntime outs xs).2 (splitRuntime outs xs).1 = xs :=
  Proofs.append_split xs

theorem read_cons {t : Ty V} (o : Origin args past t) (wires : Wires args past outs)
    (entry : Tuple F args) (locals : Locals F past) :
    Wires.read (.cons o wires) entry locals =
      .cons (readOrigin o entry locals) (wires.read entry locals) :=
  Proofs.read_cons o wires entry locals

theorem read_appended (live : Origin args past runtime) (wires : Wires args past outs)
    (entry : Tuple F args) (locals : Locals F past) :
    Wires.read (withRuntime live wires) entry locals =
      withRuntime (readOrigin live entry locals) (wires.read entry locals) :=
  Proofs.read_appended live wires entry locals

theorem erase_read (wires : Wires args past outs)
    (entry : Tuple (RuntimeValues value ρ) args) (locals : Locals (RuntimeValues value ρ) past) :
    wires.read (eraseTuple entry) (eraseLocals past locals) = eraseTuple (wires.read entry locals) :=
  Proofs.erase_read wires entry locals

theorem erase_snoc (locals : Locals (RuntimeValues value ρ) past) (xs : Tuple (RuntimeValues value ρ) outs) :
    eraseLocals (past ++ [outs]) (locals.snoc xs) = (eraseLocals past locals).snoc (eraseTuple xs) :=
  Proofs.erase_snoc locals xs

theorem erase_append (rt : ρ) (xs : Tuple (RuntimeValues value ρ) outs) :
    eraseTuple (withRuntime rt xs) = withRuntime PUnit.unit (eraseTuple xs) :=
  Proofs.erase_append rt xs

theorem erase_decode (result : Tuple (Values value) outs × ρ) :
    eraseTuple (decode result) = withRuntime PUnit.unit result.1 :=
  Proofs.erase_decode result

theorem next_decode (locals : Locals (RuntimeValues value ρ) past)
    (result : Tuple (Values value) outs × ρ) (entry : Tuple (RuntimeValues value ρ) args) :
    readOrigin (nextRuntime past outs) entry (locals.snoc (decode result)) = result.2 :=
  Proofs.next_decode locals result entry

end WireLemmas

variable {ρ : Type (max u w)} (m : Model P E (StateM ρ))

/-- The monadic and explicit-wire folds agree at every typed prefix. -/
theorem eval_run {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t)
    (entry : Tuple (RuntimeValues m.value ρ) (Threaded args))
    (locals : Locals (RuntimeValues m.value ρ) past) :
    decode ((checked.eval m (eraseTuple entry) (eraseLocals past locals)).run
      (readOrigin live entry locals)) = t.eval m.toRVSDG entry locals :=
  Proofs.eval_agrees m checked entry locals

/-- The graph computation returns exactly the explicit numbered graph's
data and final runtime, starting from any entry tuple. -/
theorem denoteGraph_run {a : Data args} {b : Data outs}
    (g : Graph (Opcode P E) (Threaded args) [] sigs (Threaded outs))
    (checked : EntryChecked a b g.toTerm)
    (input : Tuple (RuntimeValues m.value ρ) (Threaded args)) :
    decode ((denoteGraph m g checked (encode input).1).run (encode input).2) = g.run m.toRVSDG input :=
  Proofs.denote_agrees m g checked input

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured
