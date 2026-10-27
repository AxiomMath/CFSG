module

public import Certificates.Kernel.J4.Data
public import Certificates.Data.Kernel.J4Pts
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_natList CertificateChecks.KernelBounds.J4 PL
  "Certificates/Kernel/J4/data/pts.txt" 291561 9510612241972094265

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN

theorem pts_ok : j4Pts kd PL = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
