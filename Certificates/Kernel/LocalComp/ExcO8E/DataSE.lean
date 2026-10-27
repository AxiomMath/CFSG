module

public import Certificates.Kernel.LocalComp.ExcO8E.Data
public meta import Certificates.Kernel.LocalComp.ExcO8E.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelLC.ExcO8E.SE 480 9 16 CertificateChecks.KernelLC.ExcO8E.SSE
  CertificateChecks.KernelLC.ExcO8E.base4 4 CertificateChecks.KernelLC.ExcO8E.seQWords

#kss_cntord CertificateChecks.KernelLC.ExcO8E.NE CertificateChecks.KernelLC.ExcO8E.SE 480 9
  CertificateChecks.KernelLC.ExcO8E.SSE CertificateChecks.KernelLC.ExcO8E.base4
  CertificateChecks.KernelLC.ExcO8E.One480 CertificateChecks.KernelLC.ExcO8E.id480 2

#lc_reps CertificateChecks.KernelLC.ExcO8E.RE 9 CertificateChecks.KernelLC.ExcO8E.GE
  CertificateChecks.KernelLC.ExcO8E.REL

end
