module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import Certificates.Kernel.Sporadic.Fi22.H2066D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawtree CertificateChecks.KernelSpor.Fi22H3 3510 12 64 64 0
  CertificateChecks.KernelSpor.Fi22H.S3 CertificateChecks.KernelSpor.Fi22H.B 9
  CertificateChecks.KernelSpor.Fi22H.D3

end
