module

public import Certificates.Data.Kernel.OpsF2KEnum
public import Certificates.Kernel.LocalComp.J3Seeds

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.J3Enum

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CertificateChecks.KernelLC.J3Ops

theorem sylow_K : sylowCentralK 80 SA.M SB.M j3SylowCentralData = true := by decide +kernel

theorem comm_K : commTripleK 80 SA.M SB.M j3CommTripleData = true := by decide +kernel

end CertificateChecks.KernelLC.J3Enum

end
