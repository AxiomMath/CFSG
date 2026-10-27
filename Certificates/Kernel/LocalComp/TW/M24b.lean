module

public import Certificates.Data.Kernel.LocalComp.ThreeW
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuData
public import Certificates.Kernel.LocalComp.TW.Data
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness

public section

open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.Schreier CFSG.KC.LocalComp.ThreeW

set_option maxRecDepth 100000

namespace CertificateChecks.KernelLC.TW

theorem m24b_gens : listTables m24K2Gens = tabsOf m24bG := by decide +kernel

theorem m24b_invs : listInvTables m24K2Gens = tabsOf m24bI := by decide +kernel

theorem m24b_q : toTable (evalCodes m24K2Gens [2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1]) =
    tabOf m24bQ := by decide +kernel

theorem m24b_y : toTable (evalCodes m24K2Gens [2, 1, 1, 1, 2, 1, 1, 1]) = tabOf m24bY := by
  decide +kernel

theorem m24bK : threeWitnessK 24 (tabsOf m24bG) (tabsOf m24bI) (tabOf m24bQ) (tabOf m24bY) 1000 =
    true := by
  decide +kernel

end CertificateChecks.KernelLC.TW
