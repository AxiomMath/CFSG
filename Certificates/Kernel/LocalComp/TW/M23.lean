module

public import Certificates.Data.Kernel.LocalComp.ThreeW
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuData
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness

public section

open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.Schreier CFSG.KC.LocalComp.ThreeW

set_option maxRecDepth 100000

namespace CertificateChecks.KernelLC.TW

theorem m23K : threeWitnessK 23 (listTables m23KGens) (listInvTables m23KGens)
    (toTable (evalCodes m23KGens [3, 3, 3])) (toTable (evalCodes m23KGens [3, 3])) 1000 = true := by
  decide +kernel

end CertificateChecks.KernelLC.TW
