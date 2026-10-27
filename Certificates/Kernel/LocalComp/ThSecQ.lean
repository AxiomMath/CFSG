module

public import Certificates.Data.Kernel.OpsF2KQ
public import Certificates.Data.CFSGNative.Filter.ThData
public import Certificates.Kernel.EvenBN.Th8Bind

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.ThSec

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CertificateChecks.Th8

theorem sec_Q : secQ 248 SA.M SB.M thSec = true := by decide +kernel

theorem sec_negQ : (!secQ 248 SB.M SA.M thSec) = true := by decide +kernel

end CertificateChecks.KernelLC.ThSec

end
