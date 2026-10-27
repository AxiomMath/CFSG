module

public import Certificates.Data.Kernel.E7Orbit.Check
public import Certificates.Kernel.E7Orbit.Data
import CFSG.Certificates.Kernel.Common.EachTrue

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelE7Orbit ch709545n
  (CFSG.KC.E7Orbit.chunkOK CertificateChecks.KernelE7Orbit.T CertificateChecks.KernelE7Orbit.NT
    CertificateChecks.KernelE7Orbit.MS) 0 50

end
