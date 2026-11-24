module

import Silmaril.ProofFormats.DaslSyntax.Database.Examples.Model.Thms

open Silmaril.Logic.HOLLight
open Silmaril.ProofFormats.DaslSyntax.Database

example : Valid Model.standard.{0} (Tm.imp Tm.truth Tm.truth) :=
  Examples.HOL.standardValidity

#print axioms Examples.HOL.closedProof
#print axioms Examples.HOL.standardValidity
#print axioms Examples.HOL.standardValidityRow
#print axioms Model.standard
#print axioms Derives.sound
