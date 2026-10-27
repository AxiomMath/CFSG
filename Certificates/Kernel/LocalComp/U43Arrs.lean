module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Data

public section

namespace CertificateChecks.KernelLC.U43

open CFSG.EvenSmallLie.Child3.SelU43

@[expose] def autBaseArr : Array Nat := (autBase.map Fin.val).toArray
@[expose] def sylowBaseArr : Array Nat := (sylowBase.map Fin.val).toArray

end CertificateChecks.KernelLC.U43

end
