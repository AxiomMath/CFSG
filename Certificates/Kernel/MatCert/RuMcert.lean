module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.SectionRankHS.RuSeeds
public import CFSG.RankThree.Asc83Table.RuData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

theorem ru_K : mcertN (opsF2K 28) KernelSRHS.RA.M KernelSRHS.RB.M
    CFSG.RankThree.Asc83Table.Ru.ruCert = true := by
  quickRfl

theorem ru_neg : (!mcertN (opsF2K 28) KernelSRHS.RA.M KernelSRHS.RB.M
    ⟨2, [], [.eq [(0, 1)] [(1, 1)]]⟩) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
