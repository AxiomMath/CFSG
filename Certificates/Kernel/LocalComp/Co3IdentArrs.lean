module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDataInputs

public section

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3

@[expose] def invArr (i : Nat) : Array Nat := invCand 276 (genArr i)

@[expose] def inv0 : Array Nat := invArr 0
@[expose] def inv1 : Array Nat := invArr 1
@[expose] def inv2 : Array Nat := invArr 2
@[expose] def inv3 : Array Nat := invArr 3
@[expose] def inv4 : Array Nat := invArr 4
@[expose] def inv5 : Array Nat := invArr 5
@[expose] def inv6 : Array Nat := invArr 6

@[expose] def zsArr : Array Nat := compA 276 co3ZArr sArr

@[expose] def asArr : Array Nat := compA 276 aArr sArr

@[expose] def acArr : Array Nat := compA 276 aArr cArr

end CertificateChecks.KernelLC.Co3Id

end
