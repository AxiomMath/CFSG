module

public import Certificates.Kernel.Pk442010.Grp

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPk442010

open CFSG.KC.Enum CFSG.KS CFSG.KC.Pk442010

theorem gensC : allN 2 (fun k => e22 (CP.G k) tAL tAL (CP.G k)) = true ∧
    allN 4 (fun k => e22 (CQ.G k) tBL tBL (CQ.G k)) = true := by
  decide +kernel

end CertificateChecks.KernelPk442010

end
