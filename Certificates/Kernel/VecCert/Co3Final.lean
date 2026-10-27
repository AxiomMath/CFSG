module

public import Certificates.Kernel.VecCert.Co3
public import Certificates.Kernel.VecCert.Co3Bound

public section

namespace CertificateChecks.KernelVec.Co3

theorem vecCert_co3 :
    CFSG.Sporadic.SmallF2.Native.vecCert CFSG.Sporadic.Co3.Native.co3Data 3 = true :=
  ok Co3Bound.card_J_le

end CertificateChecks.KernelVec.Co3

end
