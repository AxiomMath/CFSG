module

public import Certificates.Kernel.LocalComp.M1Gen
public import Certificates.Data.Kernel.M1F2
public import Certificates.Kernel.LocalComp.ThSeeds
meta import Certificates.Kernel.LocalComp.ThSeeds
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.ThA CertificateChecks.KernelLC.thSeedA
#ks_chars CertificateChecks.KernelLC.ThB CertificateChecks.KernelLC.thSeedB
#lc_m1 CertificateChecks.KernelLC.ThA CertificateChecks.KernelLC.thSeedA 248
#lc_m1 CertificateChecks.KernelLC.ThB CertificateChecks.KernelLC.thSeedB 248

namespace CertificateChecks.KernelLC

open CFSG.KC.M1F2

theorem kThOrder : orderK 248 ThA.M ThB.M 19 5 = true := by quickRfl

end CertificateChecks.KernelLC

end
