module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import Certificates.Kernel.Sporadic.Fi22.L17337D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawtree CertificateChecks.KernelSpor.Fi22L17 3510 12 64 64 0
  CertificateChecks.KernelSpor.Fi22LD.S CertificateChecks.KernelSpor.Fi22LD.B 2
  CertificateChecks.KernelSpor.Fi22LD.D

end
