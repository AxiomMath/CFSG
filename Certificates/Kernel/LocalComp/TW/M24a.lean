module

public import Certificates.Data.Kernel.LocalComp.ThreeW
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuData
public import Certificates.Kernel.LocalComp.TW.Data
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness

public section

open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.Schreier CFSG.KC.LocalComp.ThreeW

set_option maxRecDepth 100000

namespace CertificateChecks.KernelLC.TW

theorem m24a_gens : listTables m24K1Gens = tabsOf m24aG := by decide +kernel

theorem m24a_invs : listInvTables m24K1Gens = tabsOf m24aI := by decide +kernel

theorem m24a_q : toTable (evalCodes m24K1Gens [2, 2]) = tabOf m24aQ := by decide +kernel

theorem m24a_y : toTable (evalCodes m24K1Gens [2, 1, 2, 1]) = tabOf m24aY := by decide +kernel

theorem m24aK : threeWitnessK 24 (tabsOf m24aG) (tabsOf m24aI) (tabOf m24aQ) (tabOf m24aY) 1000 =
    true := by
  decide +kernel

end CertificateChecks.KernelLC.TW
