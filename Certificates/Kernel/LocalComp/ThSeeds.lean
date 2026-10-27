module

public import Certificates.Data.CFSGNative.SectionRank.Th

public section

namespace CertificateChecks.KernelLC

@[expose] def thSeedA : String := CFSG.SectionRank.Native.thData.seedA

@[expose] def thSeedB : String := CFSG.SectionRank.Native.thData.seedB

end CertificateChecks.KernelLC

end
