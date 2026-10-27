module

public import Certificates.Kernel.Sporadic.RawGenSl
public import Certificates.Kernel.SporSch.J1.Chain
public meta import Certificates.Kernel.SporSch.J1.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl CertificateChecks.KernelSporSch.J1L 3080 12 0 64 0
  CertificateChecks.KernelSporSch.J1.strongM CertificateChecks.KernelSporSch.J1.baseM 2
  CertificateChecks.KernelSporSch.J1.derivs

end
