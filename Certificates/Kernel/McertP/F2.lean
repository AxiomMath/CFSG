module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.MatCert.J4Seeds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMP

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem j4_23_K : mcertN (opsF2K 112) KernelMC.JA.M KernelMC.JB.M
    ⟨2, [], j4_23_claims.baseFacts⟩ = true := by
  quickRfl

theorem j4_23_wf : j4_23_claims.wf = true := by decide +kernel

end CertificateChecks.KernelMP

end
