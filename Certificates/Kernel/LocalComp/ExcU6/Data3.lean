module

public import Certificates.Kernel.LocalComp.ExcU6.Data
public meta import Certificates.Kernel.LocalComp.ExcU6.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelLC.ExcU6.Q3 693 10 64 CertificateChecks.KernelLC.ExcU6.S3
  CertificateChecks.KernelLC.ExcU6.base3 11 CertificateChecks.KernelLC.ExcU6.s3QWords

#kss_cntord CertificateChecks.KernelLC.ExcU6.N3 CertificateChecks.KernelLC.ExcU6.Q3 693 10
  CertificateChecks.KernelLC.ExcU6.S3 CertificateChecks.KernelLC.ExcU6.base3
  CertificateChecks.KernelLC.ExcU6.One693 CertificateChecks.KernelLC.ExcU6.id693 2

#lc_reps CertificateChecks.KernelLC.ExcU6.R3 10 CertificateChecks.KernelLC.ExcU6.G3
  CertificateChecks.KernelLC.ExcU6.R3L

end
