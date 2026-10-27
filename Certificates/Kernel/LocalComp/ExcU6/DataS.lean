module

public import Certificates.Kernel.LocalComp.ExcU6.Data
public meta import Certificates.Kernel.LocalComp.ExcU6.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#lc_reps CertificateChecks.KernelLC.ExcU6.RS 10 CertificateChecks.KernelLC.ExcU6.SG
  CertificateChecks.KernelLC.ExcU6.RSL

end
