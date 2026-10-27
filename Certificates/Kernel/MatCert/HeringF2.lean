module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.J3Local.Seeds
public import Certificates.Kernel.SectionRankHS.RuSeeds
public import CFSG.RankThree.PartTwo.KFacts.HeringKS12J3Data
public import CFSG.RankThree.PartTwo.Sec21.Hering214KFourRuData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

theorem ks12J3_K : mcertN (opsF2K 80) KernelJ3L.JA.M KernelJ3L.JB.M
    CFSG.RankThree.PartTwo.KFacts.KS12J3.cert = true := by
  quickRfl

theorem fourRu_K : mcertN (opsF2K 28) KernelSRHS.RA.M KernelSRHS.RB.M
    CFSG.RankThree.PartTwo.Sec21.Hering214.FourRu.cert = true := by
  quickRfl

end CertificateChecks.KernelMC

end
