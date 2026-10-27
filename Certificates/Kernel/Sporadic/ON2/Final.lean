module

public import Certificates.Kernel.Sporadic.ON2.Assemble
public import Certificates.Kernel.Sporadic.ON2.MV0
public import Certificates.Kernel.Sporadic.ON2.MV1
public import Certificates.Kernel.Sporadic.ON2.MV2
public import Certificates.Kernel.Sporadic.ON2.MV3
public import Certificates.Kernel.Sporadic.ON2.MV4
public import Certificates.Kernel.Sporadic.ON2.MV5
public import Certificates.Kernel.Sporadic.ON2.MV6
public import Certificates.Kernel.Sporadic.ON2.MV7
public import Certificates.Kernel.Sporadic.ON2.OrdSort
public import Certificates.Kernel.Sporadic.ON2.Inv
public import Certificates.Kernel.Sporadic.ON2.Rel
public import Certificates.Kernel.Sporadic.ON2.Surj
public import Certificates.Kernel.Sporadic.ON2.Surj2

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ON2.mvAll CertificateChecks.KernelSpor.ON2.mvS 1023

#kon_join CertificateChecks.KernelSpor.ON2.ordAll CertificateChecks.KernelSpor.ON2.ordS 1023

#kon_join CertificateChecks.KernelSpor.ON2.sortAll CertificateChecks.KernelSpor.ON2.sortS 1023

#kon_join CertificateChecks.KernelSpor.ON2.invAll CertificateChecks.KernelSpor.ON2.invS 1023

#kon_join CertificateChecks.KernelSpor.ON2.relFAll CertificateChecks.KernelSpor.ON2.relF 154

#kon_join CertificateChecks.KernelSpor.ON2.surjFAll CertificateChecks.KernelSpor.ON2.surjF 154

namespace CertificateChecks.KernelSpor.ON2

theorem surjAll : ∀ t < 154, surjQ t = true := fun t ht => surjF_eq t ▸ surjFAll t ht

theorem relAll : ∀ t < 154, relQ t = true := fun t ht => relF_eq t ▸ relFAll t ht

theorem bridge_ok' : CFSG.Sporadic.Bridge.ONGPL.Native.bridgeCheck () = true :=
  bridge_ok mvAll ordAll sortAll invAll relAll surjAll

end CertificateChecks.KernelSpor.ON2

end
