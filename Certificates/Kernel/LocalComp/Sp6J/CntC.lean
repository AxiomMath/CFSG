module

public import Certificates.Kernel.LocalComp.Sp6J.Data
public meta import Certificates.Kernel.LocalComp.Sp6J.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_cntord CertificateChecks.KernelLC.Sp6J.N1 CertificateChecks.KernelLC.Sp6J.C1Q 36 6
  CertificateChecks.KernelLC.Sp6J.SC1 CertificateChecks.KernelLC.Sp6J.base1
  CertificateChecks.KernelLC.Sp6J.One36 CertificateChecks.KernelLC.Sp6J.id36 4

#kss_cntord CertificateChecks.KernelLC.Sp6J.N2 CertificateChecks.KernelLC.Sp6J.C2Q 36 6
  CertificateChecks.KernelLC.Sp6J.SC2 CertificateChecks.KernelLC.Sp6J.base2
  CertificateChecks.KernelLC.Sp6J.One36 CertificateChecks.KernelLC.Sp6J.id36 4

#kss_cntord CertificateChecks.KernelLC.Sp6J.N3 CertificateChecks.KernelLC.Sp6J.C3Q 36 6
  CertificateChecks.KernelLC.Sp6J.SC3 CertificateChecks.KernelLC.Sp6J.base3
  CertificateChecks.KernelLC.Sp6J.One36 CertificateChecks.KernelLC.Sp6J.id36 4

#kss_cntord CertificateChecks.KernelLC.Sp6J.N4 CertificateChecks.KernelLC.Sp6J.C4Q 36 6
  CertificateChecks.KernelLC.Sp6J.SC4 CertificateChecks.KernelLC.Sp6J.base3
  CertificateChecks.KernelLC.Sp6J.One36 CertificateChecks.KernelLC.Sp6J.id36 4

end
