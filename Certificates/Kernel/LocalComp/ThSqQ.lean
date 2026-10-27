module

public import Certificates.Data.Kernel.OpsF2KSqQ
public import Certificates.Data.WCSporRot
public import Certificates.Kernel.EvenBN.Th8Bind

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.ThSq

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CertificateChecks.Th8

theorem sq7_Q : sqQ 248 SA.M SB.M thMultData7 = true := by decide +kernel

theorem rot_Q : sqQ 248 SA.M SB.M thSevenRot = true := by decide +kernel

end CertificateChecks.KernelLC.ThSq

end
