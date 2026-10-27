module

public import Certificates.Kernel.Th.AutD.A0
public import Certificates.Kernel.Th.AutD.A1
public import Certificates.Kernel.Th.AutD.A2
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelTh.AutD.aAll CertificateChecks.KernelTh.AutD.aSl 27

end
