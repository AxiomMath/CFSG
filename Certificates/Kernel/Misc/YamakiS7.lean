module

public import Certificates.Data.Kernel.Misc.YamakiS7
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelYamakiS7

open CFSG.KD.YamakiS7 CFSG.KC.Ord

theorem s7K_true : s7K = true := by
  quickRfl

end CertificateChecks.KernelYamakiS7

end
