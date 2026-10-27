module

public import Certificates.Data.Kernel.Fi22Omega.Check
public import Certificates.Kernel.Fi22Omega.Data
import CFSG.Certificates.Kernel.Common.EachTrue

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelFi22Omega ch1023301n
  (CFSG.KC.Fi22Omega.chunkOK CertificateChecks.KernelFi22Omega.T CertificateChecks.KernelFi22Omega.NT
    CertificateChecks.KernelFi22Omega.MS) 726 966

end
