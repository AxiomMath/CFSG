module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData

public section

namespace CertificateChecks.KernelLC.Weyl

@[expose] def wBaseArr : Array Nat := (CFSG.EvenSmallLie.OmegaEight.Weyl.wBase.map Fin.val).toArray

@[expose] def nilD : List (List Int) := []

end CertificateChecks.KernelLC.Weyl

end
