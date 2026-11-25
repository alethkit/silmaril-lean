module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Functions.Thms
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Scalars.Thms

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged.Proofs

universe u

theorem domain_tuple (xs : List Value.{u}) :
    (Graph.tuple xs).domain = SetData.intRange 1 xs.length :=
  Graph.domain_ofFn _ _

theorem lookup_tuple (xs : List Value.{u}) {i : Nat} (hi : i < xs.length) :
    (Graph.tuple xs).lookup (.integer ((↑(i + 1) : Int))) = some xs[i] := by
  have hm := (SetData.integer_mem_intRange 1 xs.length ((↑(i + 1) : Int))).mpr (by omega)
  unfold Graph.tuple
  rw [Graph.lookup_ofFn hm]
  simp [hi]

theorem tuple_injective : Function.Injective Graph.tuple.{u} := by
  intro xs ys he
  have hd : SetData.intRange 1 xs.length = SetData.intRange 1 ys.length := by
    simpa only [domain_tuple] using congrArg Graph.domain he
  have length_le {xs ys : List Value.{u}}
      (h : SetData.intRange 1 xs.length = SetData.intRange 1 ys.length) :
      xs.length ≤ ys.length := by
    by_cases hz : xs.length = 0
    · omega
    · have hm : (SetData.intRange 1 xs.length).mem (.integer xs.length) :=
        (SetData.integer_mem_intRange _ _ _).mpr (by omega)
      rw [h] at hm
      have hb := (SetData.integer_mem_intRange _ _ _).mp hm
      omega
  apply List.ext_getElem (Nat.le_antisymm (length_le hd) (length_le hd.symm))
  intro i hi hj
  have hl := lookup_tuple xs hi
  rw [he, lookup_tuple ys hj] at hl
  exact (Option.some.inj hl).symm

end Silmaril.Logic.Temporal.TLA.Data.Tagged.Proofs
