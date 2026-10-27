module

public import Certificates.Kernel.LocalComp.M1Gen
public import Certificates.Kernel.LocalComp.ThSeeds
meta import Certificates.Kernel.LocalComp.ThSeeds

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.Th8.SA CertificateChecks.KernelLC.thSeedA
#ks_chars CertificateChecks.Th8.SB CertificateChecks.KernelLC.thSeedB
#lc_m1 CertificateChecks.Th8.SA CertificateChecks.KernelLC.thSeedA 248
#lc_m1 CertificateChecks.Th8.SB CertificateChecks.KernelLC.thSeedB 248

end
