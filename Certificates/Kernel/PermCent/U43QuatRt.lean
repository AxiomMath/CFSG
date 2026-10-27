module

public import Certificates.Kernel.PermCent.U43QuatP

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Quat CFSG.KC.QuatK CFSG.KS CFSG.KS.Prim
  CertificateChecks.KernelPermCent.U43P1

theorem roots_scan :
    (sqScanK 820 10 CgIn.T 1152 rF rootIdx &&
      rootIdx.all fun i => canonK 820 10 (mask 10) (820 * 10) (CgIn.T i)) = true := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
