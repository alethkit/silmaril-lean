module

public import Silmaril.SSA.MLIR.Institution.Syntax.Observational.Defs
public import Silmaril.SSA.MLIR.Institution.Arith.Defs

/-! The common slice consists of lowered scalar arithmetic blocks at typed inputs. -/

@[expose] public section

namespace Silmaril.MLIR.Institution.Syntax.Observational.Arith

open CategoryTheory
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.Institution.Arith (signature model translate)

abbrev Context := Observational.Context (fun M : Model signature => M = model)

/-- The input widths of an arithmetic block are its ordered source context. -/
def context (Γ : List Width) : Context := ⟨⟨Γ.length, Γ.get⟩⟩

/-- The common result interface has a single value at the declared width. -/
def result (w : Width) : Context := ⟨⟨1, fun _ => w⟩⟩

/-- An arithmetic block gives an arrow in the quotient for the concrete bitvector model. -/
def arrow {Γ : List Width} {w : Width} (b : Silmaril.MLIR.Arith.Block Γ w) :
    context Γ ⟶ result w :=
  ofBlock (fun _ => translate b)

end Silmaril.MLIR.Institution.Syntax.Observational.Arith
