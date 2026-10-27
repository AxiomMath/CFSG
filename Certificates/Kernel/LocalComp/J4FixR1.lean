module

public import Certificates.Data.Kernel.J4FixK
public import Certificates.Kernel.LocalComp.J4Rows
import CFSG.Certificates.Kernel.J4FixSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.J4Fix

open CFSG.KC.J4Fix CertificateChecks.KernelLC.J4R

set_option maxHeartbeats 0 in
theorem row1_K : fixRowK 112 (xK JA.M JB.M) (yK JA.M JB.M) (zK JA.M JB.M) 1 = true :=
  (fixRowFK_eq 112 _ _ _ _).symm.trans (by decide +kernel)

end CertificateChecks.KernelLC.J4Fix

end
