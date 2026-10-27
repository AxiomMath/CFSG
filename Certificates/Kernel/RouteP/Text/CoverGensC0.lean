module

public import Certificates.Kernel.RouteP.Text.CoverGensChunks
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 1000000

#kc_each CertificateChecks.KernelRouteP.pcgPc 0 8

namespace CertificateChecks.KernelRouteP

open CFSG.KC CFSG.KC.RouteP CFSG.KD.RouteP

theorem pcg_neg : (!nlChkAt CGD (fun _ => 306936) ((lnth [] pcgCs 1).map Char.toNat)
      [0, 21018, 58, 1, 0, 0] (pcgSt 2) && !nlAt 0 1 0 0 0 0 0 0 0 0 0 0) = true := by
  quickRfl

end CertificateChecks.KernelRouteP

end
