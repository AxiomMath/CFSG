module

public import Certificates.Kernel.PermCent.U43QuatP

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Quat CFSG.KC.QuatK
  CertificateChecks.KernelPermCent.U43P1

theorem ident_scan :
    identSqCheckK 820 10 eP rF (rootIdx.map CgIn.T) [(w0F, w0F)] [l0F, l1F] = true := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
