module

public import Certificates.Data.Kernel.OpsF2KCubQ
public import Certificates.Data.CFSGNative.MultRes.Witnesses
public import Certificates.Kernel.EvenBN.Th8Bind

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.ThCub

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CertificateChecks.Th8

theorem cub_Q : cubicQ 248 SA.M SB.M thMultData5 = true := by decide +kernel

end CertificateChecks.KernelLC.ThCub

end
