module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.LocalComp.ThOrder
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelMP

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem th_31_K : mcertN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M
    ⟨th_31_claims.nregs, th_31_claims.prog, th_31_claims.facts⟩ = true := by
  quickRfl

theorem th_ord4_K : mcertN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M
    ⟨th_ord4_claims.nregs, th_ord4_claims.prog, th_ord4_claims.facts⟩ = true := by
  quickRfl

end CertificateChecks.KernelMP

end
