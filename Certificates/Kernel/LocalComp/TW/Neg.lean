module

public import Certificates.Data.Kernel.LocalComp.ThreeW
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuData
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness

public section

open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.Schreier CFSG.KC.LocalComp.ThreeW

set_option maxRecDepth 100000

namespace CertificateChecks.KernelLC.TW

theorem m22_y_wrong : threeWitnessK 22 (listTables m22OKGens) (listInvTables m22OKGens)
    (toTable (evalCodes m22OKGens [1, 1])) (toTable (evalCodes m22OKGens [1, 1])) 1000 = false := by
  decide +kernel

theorem m22_ord_wrong : threeWitnessK 22 (listTables m22OKGens) (listInvTables m22OKGens)
    (toTable (evalCodes m22OKGens [1, 1])) (toTable (evalCodes m22OKGens [])) 1000 = false := by
  decide +kernel

end CertificateChecks.KernelLC.TW
