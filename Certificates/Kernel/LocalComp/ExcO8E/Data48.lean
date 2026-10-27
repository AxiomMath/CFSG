module

public import Certificates.Kernel.LocalComp.ExcO8E.Data
public meta import Certificates.Kernel.LocalComp.ExcO8E.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelLC.ExcO8E.Q48 480 9 16 CertificateChecks.KernelLC.ExcO8E.S48
  CertificateChecks.KernelLC.ExcO8E.base3 6 CertificateChecks.KernelLC.ExcO8E.s48QWords

#kss_cntord CertificateChecks.KernelLC.ExcO8E.N48 CertificateChecks.KernelLC.ExcO8E.Q48 480 9
  CertificateChecks.KernelLC.ExcO8E.S48 CertificateChecks.KernelLC.ExcO8E.base3
  CertificateChecks.KernelLC.ExcO8E.One480 CertificateChecks.KernelLC.ExcO8E.id480 2

#lc_reps CertificateChecks.KernelLC.ExcO8E.R48 9 CertificateChecks.KernelLC.ExcO8E.G48
  CertificateChecks.KernelLC.ExcO8E.R48L

end
