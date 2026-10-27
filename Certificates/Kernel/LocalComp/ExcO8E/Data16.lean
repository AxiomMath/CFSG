module

public import Certificates.Kernel.LocalComp.ExcO8E.Data
public meta import Certificates.Kernel.LocalComp.ExcO8E.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelLC.ExcO8E.Q16 480 9 16 CertificateChecks.KernelLC.ExcO8E.S16
  CertificateChecks.KernelLC.ExcO8E.base4 5 CertificateChecks.KernelLC.ExcO8E.s16QWords

#kss_cntord CertificateChecks.KernelLC.ExcO8E.N16 CertificateChecks.KernelLC.ExcO8E.Q16 480 9
  CertificateChecks.KernelLC.ExcO8E.S16 CertificateChecks.KernelLC.ExcO8E.base4
  CertificateChecks.KernelLC.ExcO8E.One480 CertificateChecks.KernelLC.ExcO8E.id480 2

#lc_reps CertificateChecks.KernelLC.ExcO8E.R16 9 CertificateChecks.KernelLC.ExcO8E.G16
  CertificateChecks.KernelLC.ExcO8E.R16L

end
