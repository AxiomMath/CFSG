module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Data

public section

namespace CertificateChecks.KernelLC.L39

open CFSG.EvenSmallLie.Child3.SelL39

@[expose] def t1BaseArr : Array Nat := (t1Base.map Fin.val).toArray
@[expose] def tBaseArr : Array Nat := (tBase.map Fin.val).toArray
@[expose] def autBaseArr : Array Nat := (autBase.map Fin.val).toArray
@[expose] def sylowBaseArr : Array Nat := (sylowBase.map Fin.val).toArray

end CertificateChecks.KernelLC.L39

end
