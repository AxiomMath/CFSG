module

public import Certificates.Kernel.LocalComp.ExcU6.Data
public meta import Certificates.Kernel.LocalComp.ExcU6.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelLC.ExcU6.Q2 693 10 64 CertificateChecks.KernelLC.ExcU6.S2
  CertificateChecks.KernelLC.ExcU6.base2 8 CertificateChecks.KernelLC.ExcU6.s2QWords

#kss_cntord CertificateChecks.KernelLC.ExcU6.N2 CertificateChecks.KernelLC.ExcU6.Q2 693 10
  CertificateChecks.KernelLC.ExcU6.S2 CertificateChecks.KernelLC.ExcU6.base2
  CertificateChecks.KernelLC.ExcU6.One693 CertificateChecks.KernelLC.ExcU6.id693 2

#lc_reps CertificateChecks.KernelLC.ExcU6.R2 10 CertificateChecks.KernelLC.ExcU6.G2
  CertificateChecks.KernelLC.ExcU6.R2L

end
