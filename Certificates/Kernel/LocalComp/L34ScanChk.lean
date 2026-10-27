module

public import Certificates.Kernel.LocalComp.L34ScanDefs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Scan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Scan
open CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB notB)

theorem kCanonC : andB (allN 64 fun c => canonK 42 6 (mask 6) (42 * 6) (L34C1.P c))
    (andB (allN 168 fun c => canonK 42 6 (mask 6) (42 * 6) (L34C2.P c))
      (allN 60 fun c => canonK 42 6 (mask 6) (42 * 6) (L34C3.P c))) = true := by
  quickRfl

theorem kNeg : notB (fixK 42 6 (pidn 42 6) 0 L34C2.P (pidn 42 6) (RP 1)) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34Scan

#kon_slices CertificateChecks.KernelLC.L34Scan.two1 0 180
#kon_slices CertificateChecks.KernelLC.L34Scan.fix2 0 180
#kon_slices CertificateChecks.KernelLC.L34Scan.fix3 0 180

#kon_join CertificateChecks.KernelLC.L34Scan.two1All CertificateChecks.KernelLC.L34Scan.two1 180
#kon_join CertificateChecks.KernelLC.L34Scan.fix2All CertificateChecks.KernelLC.L34Scan.fix2 180
#kon_join CertificateChecks.KernelLC.L34Scan.fix3All CertificateChecks.KernelLC.L34Scan.fix3 180

end
