module

public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3Ly

public section

namespace CertificateChecks.KernelLy3

open CFSG.SectionRank.Native

@[expose] def prog : List Op := lyMax7Cover3.prog

end CertificateChecks.KernelLy3

end
