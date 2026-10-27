module

public import Certificates.Kernel.TwoF4Lie.Data
public import Certificates.Data.Kernel.TwoF4LieK
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelTwoF4Lie

open CFSG.KC.Enum CFSG.KC.TwoF4LieK CFSG.KD.TwoF4Lie

theorem uRange : allN 5 (fun k => allN 1755 (fun i => Nat.blt (gp (TU k) i) 1755)) = true := by
  quickRfl

end CertificateChecks.KernelTwoF4Lie

end
