module

public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Data.Kernel.SporSch.PairK
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.PJ3WO

open CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem o17 : ordWK 6156 13 CFSG.Sporadic.Schreier.PairJ3.bs
    [PJ3.S 1, PJ3.S 1, PJ3.S 0, PJ3.S 1, PJ3.S 0, PJ3.S 1, PJ3.S 0] 17 = true := by
  quickRfl

theorem o19Neg : (ordWK 6156 13 CFSG.Sporadic.Schreier.PairJ3.bs
    [PJ3.S 1, PJ3.S 1, PJ3.S 0, PJ3.S 1, PJ3.S 0, PJ3.S 1, PJ3.S 0] 19).not = true := by
  quickRfl

end CertificateChecks.KernelSporSch.PJ3WO

end
