module

public import Certificates.Kernel.PermCent.U43QuatP
public import Certificates.Data.Kernel.QuatSpK

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.KC.QuatK CertificateChecks.KernelPermCent.U43P1

@[expose] noncomputable def spCoset (k : ℕ) : Bool :=
  spScanK 820 10 CgIn.T 1152 (sF k) eP rF u0F v0F u1F v1F l1F

end CertificateChecks.KernelPermCent.U43Quat

end
