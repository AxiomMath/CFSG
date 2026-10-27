module

public import Certificates.Kernel.HatM.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHatM

open CFSG.KC.HatChkK
open CFSG.KC.Misc.ArrEnum (arrBind)

theorem pairS1 : (List.range 512).all (fun j => fpfPairK 24 5 9 ES1.G (RA 0) (ES1.T j)) = true := by
  quickRfl

theorem greedy : arrBind (greedyF 1024 memI cmI) 1024 6 (CL 0) = true := by quickRfl

theorem cover : coverF 1024 63 memC clsC cmI = true := by quickRfl

end CertificateChecks.KernelHatM

end
