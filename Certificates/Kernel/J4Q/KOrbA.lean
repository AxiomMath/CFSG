module

public import Certificates.Kernel.J4Q.KOrbC
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Q.KBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

#j4q_all CFSG.KD.J4Q.KCA CertificateChecks.KernelJ4Q.kcA 120

end CertificateChecks.KernelJ4Q

end
