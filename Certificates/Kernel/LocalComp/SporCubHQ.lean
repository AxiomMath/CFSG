module

public import Certificates.Data.Kernel.OpsF2KCubQ
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubData
public import Certificates.Kernel.LocalComp.Co2Ops
public import Certificates.Kernel.LocalComp.Co3Ops
public import Certificates.Kernel.EvenBN.Th8Bind

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.SporCubH

open CFSG.KC.OpsF2K CFSG.AGLEmbedding.SporCubic

theorem co2_Q : cubicQ 22 Co2Ops.SA.M Co2Ops.SB.M co2Sylow5HData = true := by decide +kernel

theorem co3_Q : cubicQ 22 Co3Ops.SA.M Co3Ops.SB.M co3Sylow5HData = true := by decide +kernel

theorem th_Q : cubicQ 248 CertificateChecks.Th8.SA.M CertificateChecks.Th8.SB.M thSylow5HData =
    true := by
  decide +kernel

end CertificateChecks.KernelLC.SporCubH

end
