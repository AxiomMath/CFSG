module

public import Certificates.Kernel.VecCert.Ru
public import Certificates.Kernel.VecCert.RuBound

public section

namespace CertificateChecks.KernelVec.Ru

theorem vecCert_ru :
    CFSG.Sporadic.SmallF2.Native.vecCert CFSG.Sporadic.Ru.Native.ruData 3 = true :=
  ok RuBound.card_J_le

end CertificateChecks.KernelVec.Ru

end
