module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModelInputs

public section

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.EvenSmallLie.SympSix.Co3Ident

@[expose] def cList : Array (Array Nat) := cBFS.1
@[expose] def cPar : Array Nat := cBFS.2.1
@[expose] def cLab : Array Nat := cBFS.2.2

end CertificateChecks.KernelLC.Co3Id

end
