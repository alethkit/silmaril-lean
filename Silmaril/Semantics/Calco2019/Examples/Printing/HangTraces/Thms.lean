module

public import Silmaril.Semantics.Calco2019.Examples.Printing.HangTraces.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.PrintingHangTraces

/-! # Finite and infinite runs of the nondeterministic hang model -/

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.HangTraces

open Hangs

variable {A X Y : Type u}

instance : LawfulMonad (Traces A) := Proofs.lawful A

theorem prependWord_nil (t : Model A X) : prependWord [] t = t :=
  Proofs.prefix_nil t

theorem prependWord_append (w v : List A) (t : Model A X) :
    prependWord w (prependWord v t) = prependWord (w ++ v) t :=
  Proofs.prefix_append w v t

theorem chunkAt_some (w : ℕ → List A) (n : ℕ) (a : A) :
    chunkAt w n = some a ↔ LetterAt w n a :=
  Proofs.chunkAt_some w n a

theorem runs_nonempty (f : X → Traces A (Y ⊕ X)) (x : X) :
    ∃ t, Runs f x t :=
  Proofs.runs_nonempty f x

/-- Follow every finite or infinite run, keeping exactly its printed characters. -/
@[expose] noncomputable def iterate (f : X → Traces A (Y ⊕ X)) (x : X) : Traces A Y :=
  ⟨{t | Runs f x t}, runs_nonempty f x⟩

theorem iterate_fixpoint (f : X → Traces A (Y ⊕ X)) :
    iterate f = fun x => f x >>= Sum.elim pure (iterate f) := by
  funext x
  apply Subtype.ext
  have eq : (fun s : Y ⊕ X => ((Sum.elim pure (iterate f)) s).1) =
      Sum.elim (fun y => {Sum.inl ([], y)}) (fun z => {t | Runs f z t}) := by
    funext s
    cases s <;> rfl
  change {t | Runs f x t} = bindSet (f x).1 (fun s => ((Sum.elim pure (iterate f)) s).1)
  rw [eq]
  exact Set.ext (Proofs.runs_fixpoint f x)

/-- Prefixing a silent hang keeps the finite word before it. -/
theorem finite_hang_prefix (w : List A) :
    prependWord w (.inr Stream'.Seq.nil : Model A X) = .inr (Stream'.Seq.ofList w) :=
  congrArg Sum.inr (Stream'.Seq.append_nil _)

/-- An infinite silent loop produces the empty finite hang. -/
theorem silent_loop_hangs (A Y : Type u) :
    (.inr Stream'.Seq.nil : Model A Y) ∈
      (iterate (fun x : PUnit.{u + 1} => (pure (Sum.inr x) : Traces A (Y ⊕ PUnit.{u + 1})))
        PUnit.unit).1 :=
  Proofs.silent_loop_hangs A Y

end Silmaril.Calco2019.Examples.Printing.HangTraces
